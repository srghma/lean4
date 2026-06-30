// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Counterexample
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical Lean.Meta.Tactic.BVDecide.Normalize.Enums Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_int_neg, lean_int8_dec_le,
    lean_int8_of_nat, lean_int8_to_int, lean_int16_dec_le, lean_int16_of_nat, lean_int16_to_int,
    lean_int32_dec_le, lean_int32_of_nat, lean_int32_to_int, lean_int64_dec_le, lean_int64_of_nat,
    lean_int64_to_int_sint, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_lor, lean_nat_mul,
    lean_nat_shiftl, lean_panic_fn_borrowed, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_uint8_of_nat_mk, lean_uint8_to_nat,
    lean_uint16_of_nat_mk, lean_uint16_to_nat, lean_uint32_of_nat_mk, lean_uint32_to_nat,
    lean_uint64_of_nat, lean_uint64_of_nat_mk, lean_uint64_shift_right, lean_uint64_to_nat,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Prelude::{
    l_BitVec_ofNat, l_Lean_replaceRef, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_containsFVar, l_Lean_Expr_eqv___boxed,
    l_Lean_Expr_hash, l_Lean_Expr_hash___boxed, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isFVar, l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed,
    l_Lean_instHashableFVarId_hash, l_Lean_instHashableFVarId_hash___boxed,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkFVar,
    l_Lean_mkNatLit, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Enums::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums,
    l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::SatAtBVLogical::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ToExpr::{
    l_Lean_instToExprInt8_mkNat, l_Lean_instToExprInt16_mkNat, l_Lean_instToExprInt32_mkNat,
    l_Lean_instToExprInt64_mkNat,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_length___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7_value) as *mut leanh::LeanObject;
static mut l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0_value: leanh::LeanStringObject<43> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0_value: leanh::LeanStringObject<41> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 67, 111, 117, 110, 116, 101, 114, 101, 120, 97, 109, 112, 108, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1_value: leanh::LeanStringObject<52> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 114, 101, 99, 111, 110, 115, 116, 114, 117, 99, 116, 67, 111, 117, 110, 116, 101, 114, 69, 120, 97, 109, 112, 108, 101, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2_value: leanh::LeanStringObject<49> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 98, 105, 116, 73, 100, 120, 32, 61, 61, 32, 99, 117, 114, 114, 101, 110, 116, 66, 105, 116, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value) as *mut leanh::LeanObject,7578295756008745317 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4_value: leanh::LeanStringObject<116> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 116, m_capacity: 116, m_length: 115, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 67, 111, 117, 110, 116, 101, 114, 101, 120, 97, 109, 112, 108, 101, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 68, 105, 97, 103, 110, 111, 115, 105, 115, 77, 46, 100, 105, 97, 103, 110, 111, 115, 101, 46, 116, 114, 97, 110, 115, 102, 111, 114, 109, 69, 113, 117, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value) as *mut leanh::LeanObject,6508593840631735363 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,13801148080071449130 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value) as *mut leanh::LeanObject,17423969607579146442 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,606779917572060903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value) as *mut leanh::LeanObject,1593258566177356093 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,11609212114204283436 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value) as *mut leanh::LeanObject,4828225126264449809 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,13384902194043122320 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value) as *mut leanh::LeanObject,2954612489107370298 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,17495411711869292695 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value) as *mut leanh::LeanObject,13474504806189678690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,869628200763419231 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value) as *mut leanh::LeanObject,9755723410228041222 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,385092954486674771 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value) as *mut leanh::LeanObject,15764114953608429200 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__8_value) as *mut leanh::LeanObject,8252966037049243557 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 102, 66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__24_value) as *mut leanh::LeanObject,17737472716185871225 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__27_value) as *mut leanh::LeanObject,15761733860085307253 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__26_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__30_value) as *mut leanh::LeanObject,9255189395584251158 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 85, 73, 110, 116, 56, 32, 119, 97, 115, 32, 110, 111, 116, 32, 56, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 98, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__37_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__1_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value) as *mut leanh::LeanObject,15764114953608429200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__22_value) as *mut leanh::LeanObject,15764114953608429200 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_value) as *mut leanh::LeanObject,1458943469631247978 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 85, 73, 110, 116, 49, 54, 32, 119, 97, 115, 32, 110, 111, 116, 32, 49, 54, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value) as *mut leanh::LeanObject,9755723410228041222 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__20_value) as *mut leanh::LeanObject,9755723410228041222 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_value) as *mut leanh::LeanObject,16668572274245391716 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 85, 73, 110, 116, 51, 50, 32, 119, 97, 115, 32, 110, 111, 116, 32, 51, 50, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value) as *mut leanh::LeanObject,13474504806189678690 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__18_value) as *mut leanh::LeanObject,13474504806189678690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_value) as *mut leanh::LeanObject,16173759620455419504 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 85, 73, 110, 116, 54, 52, 32, 119, 97, 115, 32, 110, 111, 116, 32, 54, 52, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value) as *mut leanh::LeanObject,2954612489107370298 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__16_value) as *mut leanh::LeanObject,2954612489107370298 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__44_value) as *mut leanh::LeanObject,532958730868083720 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 73, 110, 116, 56, 32, 119, 97, 115, 32, 110, 111, 116, 32, 56, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67: u8 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__68_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__69_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value) as *mut leanh::LeanObject,4828225126264449809 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 115, 116, 78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__14_value) as *mut leanh::LeanObject,4828225126264449809 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_value) as *mut leanh::LeanObject,4682620960802703410 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 73, 110, 116, 49, 54, 32, 119, 97, 115, 32, 110, 111, 116, 32, 49, 54, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79: u16 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value) as *mut leanh::LeanObject,1593258566177356093 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__12_value) as *mut leanh::LeanObject,1593258566177356093 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_value) as *mut leanh::LeanObject,12385669288801998142 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 73, 110, 116, 51, 50, 32, 119, 97, 115, 32, 110, 111, 116, 32, 51, 50, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86: u32 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value) as *mut leanh::LeanObject,17423969607579146442 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__10_value) as *mut leanh::LeanObject,17423969607579146442 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_value) as *mut leanh::LeanObject,16834749042409166469 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [86, 97, 108, 117, 101, 32, 102, 111, 114, 32, 73, 110, 116, 54, 52, 32, 119, 97, 115, 32, 110, 111, 116, 32, 54, 52, 32, 98, 105, 116, 32, 98, 117, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93: u64 = 0;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value) as *mut leanh::LeanObject,6508593840631735363 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__7_value) as *mut leanh::LeanObject,6508593840631735363 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__74_value) as *mut leanh::LeanObject,6649467428781922328 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value: leanh::LeanStringObject<74> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [73, 116, 32, 97, 98, 115, 116, 114, 97, 99, 116, 101, 100, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 97, 115, 32, 111, 112, 97, 113, 117, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value: leanh::LeanStringObject<66> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [84, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 108, 121, 32, 114, 101, 108, 101, 118, 97, 110, 116, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 117, 115, 101, 100, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__1_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        84, 104, 101, 32, 112, 114, 111, 118, 101, 114, 32, 102, 111, 117, 110, 100, 32, 97, 32,
        112, 111, 116, 101, 110, 116, 105, 97, 108, 108, 121, 32, 115, 112, 117, 114, 105, 111,
        117, 115, 32, 99, 111, 117, 110, 116, 101, 114, 101, 120, 97, 109, 112, 108, 101, 58, 10,
        0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        67, 111, 110, 115, 105, 100, 101, 114, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119,
        105, 110, 103, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_value:
    leanh::LeanStringObject<71> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        84, 104, 101, 32, 112, 114, 111, 118, 101, 114, 32, 102, 111, 117, 110, 100, 32, 97, 32,
        99, 111, 117, 110, 116, 101, 114, 101, 120, 97, 109, 112, 108, 101, 44, 32, 99, 111, 110,
        115, 105, 100, 101, 114, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110,
        103, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(
    mut v_msg_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3299_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__0;
    v___f_3300_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__1;
    v___f_3301_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__2;
    v___f_3302_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__3;
    v___f_3303_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__4;
    v___f_3304_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__5;
    v___f_3305_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__6;
    v___x_3306_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3306_, 0, v___f_3299_);
    leanh::lean_ctor_set(v___x_3306_, 1, v___f_3300_);
    v___x_3307_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3307_, 0, v___x_3306_);
    leanh::lean_ctor_set(v___x_3307_, 1, v___f_3301_);
    leanh::lean_ctor_set(v___x_3307_, 2, v___f_3302_);
    leanh::lean_ctor_set(v___x_3307_, 3, v___f_3303_);
    leanh::lean_ctor_set(v___x_3307_, 4, v___f_3304_);
    v___x_3308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3308_, 0, v___x_3307_);
    leanh::lean_ctor_set(v___x_3308_, 1, v___f_3305_);
    v___x_3309_ =
        l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0___closed__7;
    v___x_3310_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3310_, 0, v___x_3309_);
    v___x_3311_ = l_instInhabitedOfMonad___redArg(v___x_3308_, v___x_3310_);
    v___x_3312_ = lean_panic_fn_borrowed(v___x_3311_, v_msg_3298_);
    leanh::lean_dec(v___x_3311_);
    return v___x_3312_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(
    mut v_k_3313_: *mut leanh::LeanObject,
    mut v_v_3314_: *mut leanh::LeanObject,
    mut v_t_3315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: u8 = 0;
    let mut v_impl_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: u8 = 0;
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v_size_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut v_unused_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut v_unused_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v_unused_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v_k_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3422_: u8 = 0;
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_unused_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut v_unused_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3445_: u8 = 0;
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3453_: u8 = 0;
    let mut v_unused_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: u8 = 0;
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3482_: u8 = 0;
    let mut v_size_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3494_: u8 = 0;
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut v_unused_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3538_: u8 = 0;
    let mut v_unused_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut v_unused_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3557_: u8 = 0;
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3565_: u8 = 0;
    let mut v_unused_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v_k_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_unused_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3593_: u8 = 0;
    let mut v_unused_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3315_) == 0 {
                    v_size_3316_ = leanh::lean_ctor_get(v_t_3315_, 0);
                    v_k_3317_ = leanh::lean_ctor_get(v_t_3315_, 1);
                    v_v_3318_ = leanh::lean_ctor_get(v_t_3315_, 2);
                    v_l_3319_ = leanh::lean_ctor_get(v_t_3315_, 3);
                    v_r_3320_ = leanh::lean_ctor_get(v_t_3315_, 4);
                    v_isSharedCheck_3601_ = (!leanh::lean_is_exclusive(v_t_3315_)) as u8;
                    if v_isSharedCheck_3601_ == 0 {
                        v___x_3322_ = v_t_3315_;
                        v_isShared_3323_ = v_isSharedCheck_3601_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_3320_);
                        leanh::lean_inc(v_l_3319_);
                        leanh::lean_inc(v_v_3318_);
                        leanh::lean_inc(v_k_3317_);
                        leanh::lean_inc(v_size_3316_);
                        leanh::lean_dec(v_t_3315_);
                        v___x_3322_ = leanh::lean_box(0);
                        v_isShared_3323_ = v_isSharedCheck_3601_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3602_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3603_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_3603_, 0, v___x_3602_);
                    leanh::lean_ctor_set(v___x_3603_, 1, v_k_3313_);
                    leanh::lean_ctor_set(v___x_3603_, 2, v_v_3314_);
                    leanh::lean_ctor_set(v___x_3603_, 3, v_t_3315_);
                    leanh::lean_ctor_set(v___x_3603_, 4, v_t_3315_);
                    return v___x_3603_;
                }
            }
            1 => {
                v___x_3324_ = lean_nat_dec_lt(v_k_3313_, v_k_3317_);
                if v___x_3324_ == 0 {
                    v___x_3325_ = lean_nat_dec_eq(v_k_3313_, v_k_3317_);
                    if v___x_3325_ == 0 {
                        leanh::lean_dec(v_size_3316_);
                        v_impl_3326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_3313_, v_v_3314_, v_r_3320_);
                        v___x_3327_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_3319_) == 0 {
                            v_size_3328_ = leanh::lean_ctor_get(v_l_3319_, 0);
                            v_size_3329_ = leanh::lean_ctor_get(v_impl_3326_, 0);
                            leanh::lean_inc(v_size_3329_);
                            v_k_3330_ = leanh::lean_ctor_get(v_impl_3326_, 1);
                            leanh::lean_inc(v_k_3330_);
                            v_v_3331_ = leanh::lean_ctor_get(v_impl_3326_, 2);
                            leanh::lean_inc(v_v_3331_);
                            v_l_3332_ = leanh::lean_ctor_get(v_impl_3326_, 3);
                            leanh::lean_inc(v_l_3332_);
                            v_r_3333_ = leanh::lean_ctor_get(v_impl_3326_, 4);
                            leanh::lean_inc(v_r_3333_);
                            v___x_3334_ = leanh::lean_unsigned_to_nat(3);
                            v___x_3335_ = lean_nat_mul(v___x_3334_, v_size_3328_);
                            v___x_3336_ = lean_nat_dec_lt(v___x_3335_, v_size_3329_);
                            leanh::lean_dec(v___x_3335_);
                            if v___x_3336_ == 0 {
                                leanh::lean_dec(v_r_3333_);
                                leanh::lean_dec(v_l_3332_);
                                leanh::lean_dec(v_v_3331_);
                                leanh::lean_dec(v_k_3330_);
                                v___x_3337_ = lean_nat_add(v___x_3327_, v_size_3328_);
                                v___x_3338_ = lean_nat_add(v___x_3337_, v_size_3329_);
                                leanh::lean_dec(v_size_3329_);
                                leanh::lean_dec(v___x_3337_);
                                if v_isShared_3323_ == 0 {
                                    leanh::lean_ctor_set(v___x_3322_, 4, v_impl_3326_);
                                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3338_);
                                    v___x_3340_ = v___x_3322_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3341_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3341_,
                                        0,
                                        v___x_3338_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3341_,
                                        1,
                                        v_k_3317_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3341_,
                                        2,
                                        v_v_3318_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3341_,
                                        3,
                                        v_l_3319_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3341_,
                                        4,
                                        v_impl_3326_,
                                    );
                                    v___x_3340_ = v_reuseFailAlloc_3341_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3405_ =
                                    (!leanh::lean_is_exclusive(v_impl_3326_)) as u8;
                                if v_isSharedCheck_3405_ == 0 {
                                    v_unused_3406_ = leanh::lean_ctor_get(v_impl_3326_, 4);
                                    leanh::lean_dec(v_unused_3406_);
                                    v_unused_3407_ = leanh::lean_ctor_get(v_impl_3326_, 3);
                                    leanh::lean_dec(v_unused_3407_);
                                    v_unused_3408_ = leanh::lean_ctor_get(v_impl_3326_, 2);
                                    leanh::lean_dec(v_unused_3408_);
                                    v_unused_3409_ = leanh::lean_ctor_get(v_impl_3326_, 1);
                                    leanh::lean_dec(v_unused_3409_);
                                    v_unused_3410_ = leanh::lean_ctor_get(v_impl_3326_, 0);
                                    leanh::lean_dec(v_unused_3410_);
                                    v___x_3343_ = v_impl_3326_;
                                    v_isShared_3344_ = v_isSharedCheck_3405_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_3326_);
                                    v___x_3343_ = leanh::lean_box(0);
                                    v_isShared_3344_ = v_isSharedCheck_3405_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3411_ = leanh::lean_ctor_get(v_impl_3326_, 3);
                            leanh::lean_inc(v_l_3411_);
                            if leanh::lean_obj_tag(v_l_3411_) == 0 {
                                v_r_3412_ = leanh::lean_ctor_get(v_impl_3326_, 4);
                                v_k_3413_ = leanh::lean_ctor_get(v_impl_3326_, 1);
                                v_v_3414_ = leanh::lean_ctor_get(v_impl_3326_, 2);
                                v_isSharedCheck_3437_ =
                                    (!leanh::lean_is_exclusive(v_impl_3326_)) as u8;
                                if v_isSharedCheck_3437_ == 0 {
                                    v_unused_3438_ = leanh::lean_ctor_get(v_impl_3326_, 3);
                                    leanh::lean_dec(v_unused_3438_);
                                    v_unused_3439_ = leanh::lean_ctor_get(v_impl_3326_, 0);
                                    leanh::lean_dec(v_unused_3439_);
                                    v___x_3416_ = v_impl_3326_;
                                    v_isShared_3417_ = v_isSharedCheck_3437_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_3412_);
                                    leanh::lean_inc(v_v_3414_);
                                    leanh::lean_inc(v_k_3413_);
                                    leanh::lean_dec(v_impl_3326_);
                                    v___x_3416_ = leanh::lean_box(0);
                                    v_isShared_3417_ = v_isSharedCheck_3437_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3440_ = leanh::lean_ctor_get(v_impl_3326_, 4);
                                leanh::lean_inc(v_r_3440_);
                                if leanh::lean_obj_tag(v_r_3440_) == 0 {
                                    v_k_3441_ = leanh::lean_ctor_get(v_impl_3326_, 1);
                                    v_v_3442_ = leanh::lean_ctor_get(v_impl_3326_, 2);
                                    v_isSharedCheck_3453_ =
                                        (!leanh::lean_is_exclusive(v_impl_3326_)) as u8;
                                    if v_isSharedCheck_3453_ == 0 {
                                        v_unused_3454_ =
                                            leanh::lean_ctor_get(v_impl_3326_, 4);
                                        leanh::lean_dec(v_unused_3454_);
                                        v_unused_3455_ =
                                            leanh::lean_ctor_get(v_impl_3326_, 3);
                                        leanh::lean_dec(v_unused_3455_);
                                        v_unused_3456_ =
                                            leanh::lean_ctor_get(v_impl_3326_, 0);
                                        leanh::lean_dec(v_unused_3456_);
                                        v___x_3444_ = v_impl_3326_;
                                        v_isShared_3445_ = v_isSharedCheck_3453_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_3442_);
                                        leanh::lean_inc(v_k_3441_);
                                        leanh::lean_dec(v_impl_3326_);
                                        v___x_3444_ = leanh::lean_box(0);
                                        v_isShared_3445_ = v_isSharedCheck_3453_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_3457_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_3323_ == 0 {
                                        leanh::lean_ctor_set(v___x_3322_, 4, v_impl_3326_);
                                        leanh::lean_ctor_set(v___x_3322_, 3, v_r_3440_);
                                        leanh::lean_ctor_set(v___x_3322_, 0, v___x_3457_);
                                        v___x_3459_ = v___x_3322_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3460_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3460_,
                                            0,
                                            v___x_3457_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3460_,
                                            1,
                                            v_k_3317_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3460_,
                                            2,
                                            v_v_3318_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3460_,
                                            3,
                                            v_r_3440_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3460_,
                                            4,
                                            v_impl_3326_,
                                        );
                                        v___x_3459_ = v_reuseFailAlloc_3460_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_3318_);
                        leanh::lean_dec(v_k_3317_);
                        if v_isShared_3323_ == 0 {
                            leanh::lean_ctor_set(v___x_3322_, 2, v_v_3314_);
                            leanh::lean_ctor_set(v___x_3322_, 1, v_k_3313_);
                            v___x_3462_ = v___x_3322_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3463_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_size_3316_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_k_3313_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_v_3314_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_l_3319_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_r_3320_);
                            v___x_3462_ = v_reuseFailAlloc_3463_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_size_3316_);
                    v_impl_3464_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_3313_, v_v_3314_, v_l_3319_);
                    v___x_3465_ = leanh::lean_unsigned_to_nat(1);
                    if leanh::lean_obj_tag(v_r_3320_) == 0 {
                        v_size_3466_ = leanh::lean_ctor_get(v_r_3320_, 0);
                        v_size_3467_ = leanh::lean_ctor_get(v_impl_3464_, 0);
                        leanh::lean_inc(v_size_3467_);
                        v_k_3468_ = leanh::lean_ctor_get(v_impl_3464_, 1);
                        leanh::lean_inc(v_k_3468_);
                        v_v_3469_ = leanh::lean_ctor_get(v_impl_3464_, 2);
                        leanh::lean_inc(v_v_3469_);
                        v_l_3470_ = leanh::lean_ctor_get(v_impl_3464_, 3);
                        leanh::lean_inc(v_l_3470_);
                        v_r_3471_ = leanh::lean_ctor_get(v_impl_3464_, 4);
                        leanh::lean_inc(v_r_3471_);
                        v___x_3472_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3473_ = lean_nat_mul(v___x_3472_, v_size_3466_);
                        v___x_3474_ = lean_nat_dec_lt(v___x_3473_, v_size_3467_);
                        leanh::lean_dec(v___x_3473_);
                        if v___x_3474_ == 0 {
                            leanh::lean_dec(v_r_3471_);
                            leanh::lean_dec(v_l_3470_);
                            leanh::lean_dec(v_v_3469_);
                            leanh::lean_dec(v_k_3468_);
                            v___x_3475_ = lean_nat_add(v___x_3465_, v_size_3467_);
                            leanh::lean_dec(v_size_3467_);
                            v___x_3476_ = lean_nat_add(v___x_3475_, v_size_3466_);
                            leanh::lean_dec(v___x_3475_);
                            if v_isShared_3323_ == 0 {
                                leanh::lean_ctor_set(v___x_3322_, 3, v_impl_3464_);
                                leanh::lean_ctor_set(v___x_3322_, 0, v___x_3476_);
                                v___x_3478_ = v___x_3322_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_3479_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3317_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3318_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3479_,
                                    3,
                                    v_impl_3464_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_r_3320_);
                                v___x_3478_ = v_reuseFailAlloc_3479_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_3545_ =
                                (!leanh::lean_is_exclusive(v_impl_3464_)) as u8;
                            if v_isSharedCheck_3545_ == 0 {
                                v_unused_3546_ = leanh::lean_ctor_get(v_impl_3464_, 4);
                                leanh::lean_dec(v_unused_3546_);
                                v_unused_3547_ = leanh::lean_ctor_get(v_impl_3464_, 3);
                                leanh::lean_dec(v_unused_3547_);
                                v_unused_3548_ = leanh::lean_ctor_get(v_impl_3464_, 2);
                                leanh::lean_dec(v_unused_3548_);
                                v_unused_3549_ = leanh::lean_ctor_get(v_impl_3464_, 1);
                                leanh::lean_dec(v_unused_3549_);
                                v_unused_3550_ = leanh::lean_ctor_get(v_impl_3464_, 0);
                                leanh::lean_dec(v_unused_3550_);
                                v___x_3481_ = v_impl_3464_;
                                v_isShared_3482_ = v_isSharedCheck_3545_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_dec(v_impl_3464_);
                                v___x_3481_ = leanh::lean_box(0);
                                v_isShared_3482_ = v_isSharedCheck_3545_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_3551_ = leanh::lean_ctor_get(v_impl_3464_, 3);
                        leanh::lean_inc(v_l_3551_);
                        if leanh::lean_obj_tag(v_l_3551_) == 0 {
                            v_r_3552_ = leanh::lean_ctor_get(v_impl_3464_, 4);
                            v_k_3553_ = leanh::lean_ctor_get(v_impl_3464_, 1);
                            v_v_3554_ = leanh::lean_ctor_get(v_impl_3464_, 2);
                            v_isSharedCheck_3565_ =
                                (!leanh::lean_is_exclusive(v_impl_3464_)) as u8;
                            if v_isSharedCheck_3565_ == 0 {
                                v_unused_3566_ = leanh::lean_ctor_get(v_impl_3464_, 3);
                                leanh::lean_dec(v_unused_3566_);
                                v_unused_3567_ = leanh::lean_ctor_get(v_impl_3464_, 0);
                                leanh::lean_dec(v_unused_3567_);
                                v___x_3556_ = v_impl_3464_;
                                v_isShared_3557_ = v_isSharedCheck_3565_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_r_3552_);
                                leanh::lean_inc(v_v_3554_);
                                leanh::lean_inc(v_k_3553_);
                                leanh::lean_dec(v_impl_3464_);
                                v___x_3556_ = leanh::lean_box(0);
                                v_isShared_3557_ = v_isSharedCheck_3565_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_3568_ = leanh::lean_ctor_get(v_impl_3464_, 4);
                            leanh::lean_inc(v_r_3568_);
                            if leanh::lean_obj_tag(v_r_3568_) == 0 {
                                v_k_3569_ = leanh::lean_ctor_get(v_impl_3464_, 1);
                                v_v_3570_ = leanh::lean_ctor_get(v_impl_3464_, 2);
                                v_isSharedCheck_3593_ =
                                    (!leanh::lean_is_exclusive(v_impl_3464_)) as u8;
                                if v_isSharedCheck_3593_ == 0 {
                                    v_unused_3594_ = leanh::lean_ctor_get(v_impl_3464_, 4);
                                    leanh::lean_dec(v_unused_3594_);
                                    v_unused_3595_ = leanh::lean_ctor_get(v_impl_3464_, 3);
                                    leanh::lean_dec(v_unused_3595_);
                                    v_unused_3596_ = leanh::lean_ctor_get(v_impl_3464_, 0);
                                    leanh::lean_dec(v_unused_3596_);
                                    v___x_3572_ = v_impl_3464_;
                                    v_isShared_3573_ = v_isSharedCheck_3593_;
                                    state = 37;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_v_3570_);
                                    leanh::lean_inc(v_k_3569_);
                                    leanh::lean_dec(v_impl_3464_);
                                    v___x_3572_ = leanh::lean_box(0);
                                    v_isShared_3573_ = v_isSharedCheck_3593_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_3597_ = leanh::lean_unsigned_to_nat(2);
                                if v_isShared_3323_ == 0 {
                                    leanh::lean_ctor_set(v___x_3322_, 4, v_r_3568_);
                                    leanh::lean_ctor_set(v___x_3322_, 3, v_impl_3464_);
                                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3597_);
                                    v___x_3599_ = v___x_3322_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3600_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3600_,
                                        0,
                                        v___x_3597_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3600_,
                                        1,
                                        v_k_3317_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3600_,
                                        2,
                                        v_v_3318_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3600_,
                                        3,
                                        v_impl_3464_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3600_,
                                        4,
                                        v_r_3568_,
                                    );
                                    v___x_3599_ = v_reuseFailAlloc_3600_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3340_;
            }
            3 => {
                v_size_3345_ = leanh::lean_ctor_get(v_l_3332_, 0);
                v_k_3346_ = leanh::lean_ctor_get(v_l_3332_, 1);
                v_v_3347_ = leanh::lean_ctor_get(v_l_3332_, 2);
                v_l_3348_ = leanh::lean_ctor_get(v_l_3332_, 3);
                v_r_3349_ = leanh::lean_ctor_get(v_l_3332_, 4);
                v_size_3350_ = leanh::lean_ctor_get(v_r_3333_, 0);
                v___x_3351_ = leanh::lean_unsigned_to_nat(2);
                v___x_3352_ = lean_nat_mul(v___x_3351_, v_size_3350_);
                v___x_3353_ = lean_nat_dec_lt(v_size_3345_, v___x_3352_);
                leanh::lean_dec(v___x_3352_);
                if v___x_3353_ == 0 {
                    leanh::lean_inc(v_r_3349_);
                    leanh::lean_inc(v_l_3348_);
                    leanh::lean_inc(v_v_3347_);
                    leanh::lean_inc(v_k_3346_);
                    v_isSharedCheck_3381_ = (!leanh::lean_is_exclusive(v_l_3332_)) as u8;
                    if v_isSharedCheck_3381_ == 0 {
                        v_unused_3382_ = leanh::lean_ctor_get(v_l_3332_, 4);
                        leanh::lean_dec(v_unused_3382_);
                        v_unused_3383_ = leanh::lean_ctor_get(v_l_3332_, 3);
                        leanh::lean_dec(v_unused_3383_);
                        v_unused_3384_ = leanh::lean_ctor_get(v_l_3332_, 2);
                        leanh::lean_dec(v_unused_3384_);
                        v_unused_3385_ = leanh::lean_ctor_get(v_l_3332_, 1);
                        leanh::lean_dec(v_unused_3385_);
                        v_unused_3386_ = leanh::lean_ctor_get(v_l_3332_, 0);
                        leanh::lean_dec(v_unused_3386_);
                        v___x_3355_ = v_l_3332_;
                        v_isShared_3356_ = v_isSharedCheck_3381_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_3332_);
                        v___x_3355_ = leanh::lean_box(0);
                        v_isShared_3356_ = v_isSharedCheck_3381_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3322_);
                    v___x_3387_ = lean_nat_add(v___x_3327_, v_size_3328_);
                    v___x_3388_ = lean_nat_add(v___x_3387_, v_size_3329_);
                    leanh::lean_dec(v_size_3329_);
                    v___x_3389_ = lean_nat_add(v___x_3387_, v_size_3345_);
                    leanh::lean_dec(v___x_3387_);
                    leanh::lean_inc_ref(v_l_3319_);
                    if v_isShared_3344_ == 0 {
                        leanh::lean_ctor_set(v___x_3343_, 4, v_l_3332_);
                        leanh::lean_ctor_set(v___x_3343_, 3, v_l_3319_);
                        leanh::lean_ctor_set(v___x_3343_, 2, v_v_3318_);
                        leanh::lean_ctor_set(v___x_3343_, 1, v_k_3317_);
                        leanh::lean_ctor_set(v___x_3343_, 0, v___x_3389_);
                        v___x_3391_ = v___x_3343_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3404_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3389_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_k_3317_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_v_3318_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_l_3319_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 4, v_l_3332_);
                        v___x_3391_ = v_reuseFailAlloc_3404_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3357_ = lean_nat_add(v___x_3327_, v_size_3328_);
                v___x_3358_ = lean_nat_add(v___x_3357_, v_size_3329_);
                leanh::lean_dec(v_size_3329_);
                if leanh::lean_obj_tag(v_l_3348_) == 0 {
                    v_size_3379_ = leanh::lean_ctor_get(v_l_3348_, 0);
                    leanh::lean_inc(v_size_3379_);
                    v___y_3371_ = v_size_3379_;
                    state = 8;
                    continue;
                } else {
                    v___x_3380_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3371_ = v___x_3380_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3363_ = lean_nat_add(v___y_3361_, v___y_3362_);
                leanh::lean_dec(v___y_3362_);
                leanh::lean_dec(v___y_3361_);
                if v_isShared_3356_ == 0 {
                    leanh::lean_ctor_set(v___x_3355_, 4, v_r_3333_);
                    leanh::lean_ctor_set(v___x_3355_, 3, v_r_3349_);
                    leanh::lean_ctor_set(v___x_3355_, 2, v_v_3331_);
                    leanh::lean_ctor_set(v___x_3355_, 1, v_k_3330_);
                    leanh::lean_ctor_set(v___x_3355_, 0, v___x_3363_);
                    v___x_3365_ = v___x_3355_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_r_3349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_r_3333_);
                    v___x_3365_ = v_reuseFailAlloc_3369_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3344_ == 0 {
                    leanh::lean_ctor_set(v___x_3343_, 4, v___x_3365_);
                    leanh::lean_ctor_set(v___x_3343_, 3, v___y_3360_);
                    leanh::lean_ctor_set(v___x_3343_, 2, v_v_3347_);
                    leanh::lean_ctor_set(v___x_3343_, 1, v_k_3346_);
                    leanh::lean_ctor_set(v___x_3343_, 0, v___x_3358_);
                    v___x_3367_ = v___x_3343_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3368_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 3, v___y_3360_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 4, v___x_3365_);
                    v___x_3367_ = v_reuseFailAlloc_3368_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3367_;
            }
            8 => {
                v___x_3372_ = lean_nat_add(v___x_3357_, v___y_3371_);
                leanh::lean_dec(v___y_3371_);
                leanh::lean_dec(v___x_3357_);
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 4, v_l_3348_);
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3372_);
                    v___x_3374_ = v___x_3322_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_l_3319_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_l_3348_);
                    v___x_3374_ = v_reuseFailAlloc_3378_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3375_ = lean_nat_add(v___x_3327_, v_size_3350_);
                if leanh::lean_obj_tag(v_r_3349_) == 0 {
                    v_size_3376_ = leanh::lean_ctor_get(v_r_3349_, 0);
                    leanh::lean_inc(v_size_3376_);
                    v___y_3360_ = v___x_3374_;
                    v___y_3361_ = v___x_3375_;
                    v___y_3362_ = v_size_3376_;
                    state = 5;
                    continue;
                } else {
                    v___x_3377_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3360_ = v___x_3374_;
                    v___y_3361_ = v___x_3375_;
                    v___y_3362_ = v___x_3377_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3398_ = (!leanh::lean_is_exclusive(v_l_3319_)) as u8;
                if v_isSharedCheck_3398_ == 0 {
                    v_unused_3399_ = leanh::lean_ctor_get(v_l_3319_, 4);
                    leanh::lean_dec(v_unused_3399_);
                    v_unused_3400_ = leanh::lean_ctor_get(v_l_3319_, 3);
                    leanh::lean_dec(v_unused_3400_);
                    v_unused_3401_ = leanh::lean_ctor_get(v_l_3319_, 2);
                    leanh::lean_dec(v_unused_3401_);
                    v_unused_3402_ = leanh::lean_ctor_get(v_l_3319_, 1);
                    leanh::lean_dec(v_unused_3402_);
                    v_unused_3403_ = leanh::lean_ctor_get(v_l_3319_, 0);
                    leanh::lean_dec(v_unused_3403_);
                    v___x_3393_ = v_l_3319_;
                    v_isShared_3394_ = v_isSharedCheck_3398_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_l_3319_);
                    v___x_3393_ = leanh::lean_box(0);
                    v_isShared_3394_ = v_isSharedCheck_3398_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3394_ == 0 {
                    leanh::lean_ctor_set(v___x_3393_, 4, v_r_3333_);
                    leanh::lean_ctor_set(v___x_3393_, 3, v___x_3391_);
                    leanh::lean_ctor_set(v___x_3393_, 2, v_v_3331_);
                    leanh::lean_ctor_set(v___x_3393_, 1, v_k_3330_);
                    leanh::lean_ctor_set(v___x_3393_, 0, v___x_3388_);
                    v___x_3396_ = v___x_3393_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3397_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_k_3330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_v_3331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 3, v___x_3391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 4, v_r_3333_);
                    v___x_3396_ = v_reuseFailAlloc_3397_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3396_;
            }
            13 => {
                v_k_3418_ = leanh::lean_ctor_get(v_l_3411_, 1);
                v_v_3419_ = leanh::lean_ctor_get(v_l_3411_, 2);
                v_isSharedCheck_3433_ = (!leanh::lean_is_exclusive(v_l_3411_)) as u8;
                if v_isSharedCheck_3433_ == 0 {
                    v_unused_3434_ = leanh::lean_ctor_get(v_l_3411_, 4);
                    leanh::lean_dec(v_unused_3434_);
                    v_unused_3435_ = leanh::lean_ctor_get(v_l_3411_, 3);
                    leanh::lean_dec(v_unused_3435_);
                    v_unused_3436_ = leanh::lean_ctor_get(v_l_3411_, 0);
                    leanh::lean_dec(v_unused_3436_);
                    v___x_3421_ = v_l_3411_;
                    v_isShared_3422_ = v_isSharedCheck_3433_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3419_);
                    leanh::lean_inc(v_k_3418_);
                    leanh::lean_dec(v_l_3411_);
                    v___x_3421_ = leanh::lean_box(0);
                    v_isShared_3422_ = v_isSharedCheck_3433_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3423_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_3412_, 2);
                if v_isShared_3422_ == 0 {
                    leanh::lean_ctor_set(v___x_3421_, 4, v_r_3412_);
                    leanh::lean_ctor_set(v___x_3421_, 3, v_r_3412_);
                    leanh::lean_ctor_set(v___x_3421_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v___x_3421_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v___x_3421_, 0, v___x_3327_);
                    v___x_3425_ = v___x_3421_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_r_3412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 4, v_r_3412_);
                    v___x_3425_ = v_reuseFailAlloc_3432_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v_r_3412_);
                if v_isShared_3417_ == 0 {
                    leanh::lean_ctor_set(v___x_3416_, 3, v_r_3412_);
                    leanh::lean_ctor_set(v___x_3416_, 0, v___x_3327_);
                    v___x_3427_ = v___x_3416_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3431_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_k_3413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_v_3414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_r_3412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_r_3412_);
                    v___x_3427_ = v_reuseFailAlloc_3431_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 4, v___x_3427_);
                    leanh::lean_ctor_set(v___x_3322_, 3, v___x_3425_);
                    leanh::lean_ctor_set(v___x_3322_, 2, v_v_3419_);
                    leanh::lean_ctor_set(v___x_3322_, 1, v_k_3418_);
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3423_);
                    v___x_3429_ = v___x_3322_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3430_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3423_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_k_3418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 2, v_v_3419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 3, v___x_3425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3430_, 4, v___x_3427_);
                    v___x_3429_ = v_reuseFailAlloc_3430_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3429_;
            }
            18 => {
                v___x_3446_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3445_ == 0 {
                    leanh::lean_ctor_set(v___x_3444_, 4, v_l_3411_);
                    leanh::lean_ctor_set(v___x_3444_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v___x_3444_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v___x_3444_, 0, v___x_3327_);
                    v___x_3448_ = v___x_3444_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_l_3411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_l_3411_);
                    v___x_3448_ = v_reuseFailAlloc_3452_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 4, v_r_3440_);
                    leanh::lean_ctor_set(v___x_3322_, 3, v___x_3448_);
                    leanh::lean_ctor_set(v___x_3322_, 2, v_v_3442_);
                    leanh::lean_ctor_set(v___x_3322_, 1, v_k_3441_);
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3446_);
                    v___x_3450_ = v___x_3322_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 3, v___x_3448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_r_3440_);
                    v___x_3450_ = v_reuseFailAlloc_3451_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3450_;
            }
            21 => {
                return v___x_3459_;
            }
            22 => {
                return v___x_3462_;
            }
            23 => {
                return v___x_3478_;
            }
            24 => {
                v_size_3483_ = leanh::lean_ctor_get(v_l_3470_, 0);
                v_size_3484_ = leanh::lean_ctor_get(v_r_3471_, 0);
                v_k_3485_ = leanh::lean_ctor_get(v_r_3471_, 1);
                v_v_3486_ = leanh::lean_ctor_get(v_r_3471_, 2);
                v_l_3487_ = leanh::lean_ctor_get(v_r_3471_, 3);
                v_r_3488_ = leanh::lean_ctor_get(v_r_3471_, 4);
                v___x_3489_ = leanh::lean_unsigned_to_nat(2);
                v___x_3490_ = lean_nat_mul(v___x_3489_, v_size_3483_);
                v___x_3491_ = lean_nat_dec_lt(v_size_3484_, v___x_3490_);
                leanh::lean_dec(v___x_3490_);
                if v___x_3491_ == 0 {
                    leanh::lean_inc(v_r_3488_);
                    leanh::lean_inc(v_l_3487_);
                    leanh::lean_inc(v_v_3486_);
                    leanh::lean_inc(v_k_3485_);
                    v_isSharedCheck_3520_ = (!leanh::lean_is_exclusive(v_r_3471_)) as u8;
                    if v_isSharedCheck_3520_ == 0 {
                        v_unused_3521_ = leanh::lean_ctor_get(v_r_3471_, 4);
                        leanh::lean_dec(v_unused_3521_);
                        v_unused_3522_ = leanh::lean_ctor_get(v_r_3471_, 3);
                        leanh::lean_dec(v_unused_3522_);
                        v_unused_3523_ = leanh::lean_ctor_get(v_r_3471_, 2);
                        leanh::lean_dec(v_unused_3523_);
                        v_unused_3524_ = leanh::lean_ctor_get(v_r_3471_, 1);
                        leanh::lean_dec(v_unused_3524_);
                        v_unused_3525_ = leanh::lean_ctor_get(v_r_3471_, 0);
                        leanh::lean_dec(v_unused_3525_);
                        v___x_3493_ = v_r_3471_;
                        v_isShared_3494_ = v_isSharedCheck_3520_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_3471_);
                        v___x_3493_ = leanh::lean_box(0);
                        v_isShared_3494_ = v_isSharedCheck_3520_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3322_);
                    v___x_3526_ = lean_nat_add(v___x_3465_, v_size_3467_);
                    leanh::lean_dec(v_size_3467_);
                    v___x_3527_ = lean_nat_add(v___x_3526_, v_size_3466_);
                    leanh::lean_dec(v___x_3526_);
                    v___x_3528_ = lean_nat_add(v___x_3465_, v_size_3466_);
                    v___x_3529_ = lean_nat_add(v___x_3528_, v_size_3484_);
                    leanh::lean_dec(v___x_3528_);
                    leanh::lean_inc_ref(v_r_3320_);
                    if v_isShared_3482_ == 0 {
                        leanh::lean_ctor_set(v___x_3481_, 4, v_r_3320_);
                        leanh::lean_ctor_set(v___x_3481_, 3, v_r_3471_);
                        leanh::lean_ctor_set(v___x_3481_, 2, v_v_3318_);
                        leanh::lean_ctor_set(v___x_3481_, 1, v_k_3317_);
                        leanh::lean_ctor_set(v___x_3481_, 0, v___x_3529_);
                        v___x_3531_ = v___x_3481_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3544_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3529_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_k_3317_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_v_3318_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_r_3471_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_r_3320_);
                        v___x_3531_ = v_reuseFailAlloc_3544_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3495_ = lean_nat_add(v___x_3465_, v_size_3467_);
                leanh::lean_dec(v_size_3467_);
                v___x_3496_ = lean_nat_add(v___x_3495_, v_size_3466_);
                leanh::lean_dec(v___x_3495_);
                v___x_3508_ = lean_nat_add(v___x_3465_, v_size_3483_);
                if leanh::lean_obj_tag(v_l_3487_) == 0 {
                    v_size_3518_ = leanh::lean_ctor_get(v_l_3487_, 0);
                    leanh::lean_inc(v_size_3518_);
                    v___y_3510_ = v_size_3518_;
                    state = 29;
                    continue;
                } else {
                    v___x_3519_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3510_ = v___x_3519_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3501_ = lean_nat_add(v___y_3498_, v___y_3500_);
                leanh::lean_dec(v___y_3500_);
                leanh::lean_dec(v___y_3498_);
                if v_isShared_3494_ == 0 {
                    leanh::lean_ctor_set(v___x_3493_, 4, v_r_3320_);
                    leanh::lean_ctor_set(v___x_3493_, 3, v_r_3488_);
                    leanh::lean_ctor_set(v___x_3493_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v___x_3493_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v___x_3493_, 0, v___x_3501_);
                    v___x_3503_ = v___x_3493_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_r_3488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 4, v_r_3320_);
                    v___x_3503_ = v_reuseFailAlloc_3507_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3482_ == 0 {
                    leanh::lean_ctor_set(v___x_3481_, 4, v___x_3503_);
                    leanh::lean_ctor_set(v___x_3481_, 3, v___y_3499_);
                    leanh::lean_ctor_set(v___x_3481_, 2, v_v_3486_);
                    leanh::lean_ctor_set(v___x_3481_, 1, v_k_3485_);
                    leanh::lean_ctor_set(v___x_3481_, 0, v___x_3496_);
                    v___x_3505_ = v___x_3481_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3506_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_k_3485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_v_3486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 3, v___y_3499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 4, v___x_3503_);
                    v___x_3505_ = v_reuseFailAlloc_3506_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3505_;
            }
            29 => {
                v___x_3511_ = lean_nat_add(v___x_3508_, v___y_3510_);
                leanh::lean_dec(v___y_3510_);
                leanh::lean_dec(v___x_3508_);
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 4, v_l_3487_);
                    leanh::lean_ctor_set(v___x_3322_, 3, v_l_3470_);
                    leanh::lean_ctor_set(v___x_3322_, 2, v_v_3469_);
                    leanh::lean_ctor_set(v___x_3322_, 1, v_k_3468_);
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3511_);
                    v___x_3513_ = v___x_3322_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_k_3468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_v_3469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 3, v_l_3470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 4, v_l_3487_);
                    v___x_3513_ = v_reuseFailAlloc_3517_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3514_ = lean_nat_add(v___x_3465_, v_size_3466_);
                if leanh::lean_obj_tag(v_r_3488_) == 0 {
                    v_size_3515_ = leanh::lean_ctor_get(v_r_3488_, 0);
                    leanh::lean_inc(v_size_3515_);
                    v___y_3498_ = v___x_3514_;
                    v___y_3499_ = v___x_3513_;
                    v___y_3500_ = v_size_3515_;
                    state = 26;
                    continue;
                } else {
                    v___x_3516_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3498_ = v___x_3514_;
                    v___y_3499_ = v___x_3513_;
                    v___y_3500_ = v___x_3516_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3538_ = (!leanh::lean_is_exclusive(v_r_3320_)) as u8;
                if v_isSharedCheck_3538_ == 0 {
                    v_unused_3539_ = leanh::lean_ctor_get(v_r_3320_, 4);
                    leanh::lean_dec(v_unused_3539_);
                    v_unused_3540_ = leanh::lean_ctor_get(v_r_3320_, 3);
                    leanh::lean_dec(v_unused_3540_);
                    v_unused_3541_ = leanh::lean_ctor_get(v_r_3320_, 2);
                    leanh::lean_dec(v_unused_3541_);
                    v_unused_3542_ = leanh::lean_ctor_get(v_r_3320_, 1);
                    leanh::lean_dec(v_unused_3542_);
                    v_unused_3543_ = leanh::lean_ctor_get(v_r_3320_, 0);
                    leanh::lean_dec(v_unused_3543_);
                    v___x_3533_ = v_r_3320_;
                    v_isShared_3534_ = v_isSharedCheck_3538_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_r_3320_);
                    v___x_3533_ = leanh::lean_box(0);
                    v_isShared_3534_ = v_isSharedCheck_3538_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3534_ == 0 {
                    leanh::lean_ctor_set(v___x_3533_, 4, v___x_3531_);
                    leanh::lean_ctor_set(v___x_3533_, 3, v_l_3470_);
                    leanh::lean_ctor_set(v___x_3533_, 2, v_v_3469_);
                    leanh::lean_ctor_set(v___x_3533_, 1, v_k_3468_);
                    leanh::lean_ctor_set(v___x_3533_, 0, v___x_3527_);
                    v___x_3536_ = v___x_3533_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3537_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_l_3470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 4, v___x_3531_);
                    v___x_3536_ = v_reuseFailAlloc_3537_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3536_;
            }
            34 => {
                v___x_3558_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_3552_);
                if v_isShared_3557_ == 0 {
                    leanh::lean_ctor_set(v___x_3556_, 3, v_r_3552_);
                    leanh::lean_ctor_set(v___x_3556_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v___x_3556_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v___x_3556_, 0, v___x_3465_);
                    v___x_3560_ = v___x_3556_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3564_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_r_3552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_r_3552_);
                    v___x_3560_ = v_reuseFailAlloc_3564_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 4, v___x_3560_);
                    leanh::lean_ctor_set(v___x_3322_, 3, v_l_3551_);
                    leanh::lean_ctor_set(v___x_3322_, 2, v_v_3554_);
                    leanh::lean_ctor_set(v___x_3322_, 1, v_k_3553_);
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3558_);
                    v___x_3562_ = v___x_3322_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_k_3553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_v_3554_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_l_3551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 4, v___x_3560_);
                    v___x_3562_ = v_reuseFailAlloc_3563_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3562_;
            }
            37 => {
                v_k_3574_ = leanh::lean_ctor_get(v_r_3568_, 1);
                v_v_3575_ = leanh::lean_ctor_get(v_r_3568_, 2);
                v_isSharedCheck_3589_ = (!leanh::lean_is_exclusive(v_r_3568_)) as u8;
                if v_isSharedCheck_3589_ == 0 {
                    v_unused_3590_ = leanh::lean_ctor_get(v_r_3568_, 4);
                    leanh::lean_dec(v_unused_3590_);
                    v_unused_3591_ = leanh::lean_ctor_get(v_r_3568_, 3);
                    leanh::lean_dec(v_unused_3591_);
                    v_unused_3592_ = leanh::lean_ctor_get(v_r_3568_, 0);
                    leanh::lean_dec(v_unused_3592_);
                    v___x_3577_ = v_r_3568_;
                    v_isShared_3578_ = v_isSharedCheck_3589_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_v_3575_);
                    leanh::lean_inc(v_k_3574_);
                    leanh::lean_dec(v_r_3568_);
                    v___x_3577_ = leanh::lean_box(0);
                    v_isShared_3578_ = v_isSharedCheck_3589_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3579_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_3578_ == 0 {
                    leanh::lean_ctor_set(v___x_3577_, 4, v_l_3551_);
                    leanh::lean_ctor_set(v___x_3577_, 3, v_l_3551_);
                    leanh::lean_ctor_set(v___x_3577_, 2, v_v_3570_);
                    leanh::lean_ctor_set(v___x_3577_, 1, v_k_3569_);
                    leanh::lean_ctor_set(v___x_3577_, 0, v___x_3465_);
                    v___x_3581_ = v___x_3577_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_v_3570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_l_3551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_l_3551_);
                    v___x_3581_ = v_reuseFailAlloc_3588_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3573_ == 0 {
                    leanh::lean_ctor_set(v___x_3572_, 4, v_l_3551_);
                    leanh::lean_ctor_set(v___x_3572_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v___x_3572_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v___x_3572_, 0, v___x_3465_);
                    v___x_3583_ = v___x_3572_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3587_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3318_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_l_3551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_l_3551_);
                    v___x_3583_ = v_reuseFailAlloc_3587_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3323_ == 0 {
                    leanh::lean_ctor_set(v___x_3322_, 4, v___x_3583_);
                    leanh::lean_ctor_set(v___x_3322_, 3, v___x_3581_);
                    leanh::lean_ctor_set(v___x_3322_, 2, v_v_3575_);
                    leanh::lean_ctor_set(v___x_3322_, 1, v_k_3574_);
                    leanh::lean_ctor_set(v___x_3322_, 0, v___x_3579_);
                    v___x_3585_ = v___x_3322_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3586_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_k_3574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_v_3575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 3, v___x_3581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 4, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3586_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3585_;
            }
            42 => {
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_fallback_3605_: *mut leanh::LeanObject,
    mut v_x_3606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3606_) == 0 {
                    leanh::lean_inc(v_fallback_3605_);
                    return v_fallback_3605_;
                } else {
                    v_key_3607_ = leanh::lean_ctor_get(v_x_3606_, 0);
                    v_value_3608_ = leanh::lean_ctor_get(v_x_3606_, 1);
                    v_tail_3609_ = leanh::lean_ctor_get(v_x_3606_, 2);
                    v___x_3610_ = lean_nat_dec_eq(v_key_3607_, v_a_3604_);
                    if v___x_3610_ == 0 {
                        v_x_3606_ = v_tail_3609_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3608_);
                        return v_value_3608_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg___boxed(
    mut v_a_3612_: *mut leanh::LeanObject,
    mut v_fallback_3613_: *mut leanh::LeanObject,
    mut v_x_3614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3615_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_3612_, v_fallback_3613_, v_x_3614_);
    leanh::lean_dec(v_x_3614_);
    leanh::lean_dec(v_fallback_3613_);
    leanh::lean_dec(v_a_3612_);
    return v_res_3615_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(
    mut v_m_3616_: *mut leanh::LeanObject,
    mut v_a_3617_: *mut leanh::LeanObject,
    mut v_fallback_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: u64 = 0;
    let mut v___x_3622_: u64 = 0;
    let mut v___x_3623_: u64 = 0;
    let mut v_fold_3624_: u64 = 0;
    let mut v___x_3625_: u64 = 0;
    let mut v___x_3626_: u64 = 0;
    let mut v___x_3627_: u64 = 0;
    let mut v___x_3628_: usize = 0;
    let mut v___x_3629_: usize = 0;
    let mut v___x_3630_: usize = 0;
    let mut v___x_3631_: usize = 0;
    let mut v___x_3632_: usize = 0;
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3619_ = leanh::lean_ctor_get(v_m_3616_, 1);
    v___x_3620_ = lean_array_get_size(v_buckets_3619_);
    v___x_3621_ = lean_uint64_of_nat(v_a_3617_);
    v___x_3622_ = 32u64;
    v___x_3623_ = lean_uint64_shift_right(v___x_3621_, v___x_3622_);
    v_fold_3624_ = lean_uint64_xor(v___x_3621_, v___x_3623_);
    v___x_3625_ = 16u64;
    v___x_3626_ = lean_uint64_shift_right(v_fold_3624_, v___x_3625_);
    v___x_3627_ = lean_uint64_xor(v_fold_3624_, v___x_3626_);
    v___x_3628_ = lean_uint64_to_usize(v___x_3627_);
    v___x_3629_ = lean_usize_of_nat(v___x_3620_);
    v___x_3630_ = 1usize;
    v___x_3631_ = lean_usize_sub(v___x_3629_, v___x_3630_);
    v___x_3632_ = lean_usize_land(v___x_3628_, v___x_3631_);
    v___x_3633_ = lean_array_uget_borrowed(v_buckets_3619_, v___x_3632_);
    v___x_3634_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_3617_, v_fallback_3618_, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg___boxed(
    mut v_m_3635_: *mut leanh::LeanObject,
    mut v_a_3636_: *mut leanh::LeanObject,
    mut v_fallback_3637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3638_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_3635_, v_a_3636_, v_fallback_3637_);
    leanh::lean_dec(v_fallback_3637_);
    leanh::lean_dec(v_a_3636_);
    leanh::lean_dec_ref(v_m_3635_);
    return v_res_3638_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(
    mut v_a_3639_: *mut leanh::LeanObject,
    mut v_x_3640_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3641_: u8 = 0;
    let mut v_key_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3640_) == 0 {
                    v___x_3641_ = 0;
                    return v___x_3641_;
                } else {
                    v_key_3642_ = leanh::lean_ctor_get(v_x_3640_, 0);
                    v_tail_3643_ = leanh::lean_ctor_get(v_x_3640_, 2);
                    v___x_3644_ = lean_nat_dec_eq(v_key_3642_, v_a_3639_);
                    if v___x_3644_ == 0 {
                        v_x_3640_ = v_tail_3643_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3644_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg___boxed(
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_x_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3648_: u8 = 0;
    let mut v_r_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_3646_, v_x_3647_);
    leanh::lean_dec(v_x_3647_);
    leanh::lean_dec(v_a_3646_);
    v_r_3649_ = leanh::lean_box((v_res_3648_) as usize);
    return v_r_3649_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(
    mut v_a_3650_: *mut leanh::LeanObject,
    mut v_b_3651_: *mut leanh::LeanObject,
    mut v_x_3652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3652_) == 0 {
                    leanh::lean_dec(v_b_3651_);
                    leanh::lean_dec(v_a_3650_);
                    return v_x_3652_;
                } else {
                    v_key_3653_ = leanh::lean_ctor_get(v_x_3652_, 0);
                    v_value_3654_ = leanh::lean_ctor_get(v_x_3652_, 1);
                    v_tail_3655_ = leanh::lean_ctor_get(v_x_3652_, 2);
                    v_isSharedCheck_3667_ = (!leanh::lean_is_exclusive(v_x_3652_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3657_ = v_x_3652_;
                        v_isShared_3658_ = v_isSharedCheck_3667_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3655_);
                        leanh::lean_inc(v_value_3654_);
                        leanh::lean_inc(v_key_3653_);
                        leanh::lean_dec(v_x_3652_);
                        v___x_3657_ = leanh::lean_box(0);
                        v_isShared_3658_ = v_isSharedCheck_3667_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3659_ = lean_nat_dec_eq(v_key_3653_, v_a_3650_);
                if v___x_3659_ == 0 {
                    v___x_3660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_3650_, v_b_3651_, v_tail_3655_);
                    if v_isShared_3658_ == 0 {
                        leanh::lean_ctor_set(v___x_3657_, 2, v___x_3660_);
                        v___x_3662_ = v___x_3657_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_key_3653_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_value_3654_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 2, v___x_3660_);
                        v___x_3662_ = v_reuseFailAlloc_3663_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3654_);
                    leanh::lean_dec(v_key_3653_);
                    if v_isShared_3658_ == 0 {
                        leanh::lean_ctor_set(v___x_3657_, 1, v_b_3651_);
                        leanh::lean_ctor_set(v___x_3657_, 0, v_a_3650_);
                        v___x_3665_ = v___x_3657_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3666_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3650_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_b_3651_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_tail_3655_);
                        v___x_3665_ = v_reuseFailAlloc_3666_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3662_;
            }
            3 => {
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(
    mut v_x_3668_: *mut leanh::LeanObject,
    mut v_x_3669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3675_: u8 = 0;
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: u64 = 0;
    let mut v___x_3678_: u64 = 0;
    let mut v___x_3679_: u64 = 0;
    let mut v_fold_3680_: u64 = 0;
    let mut v___x_3681_: u64 = 0;
    let mut v___x_3682_: u64 = 0;
    let mut v___x_3683_: u64 = 0;
    let mut v___x_3684_: usize = 0;
    let mut v___x_3685_: usize = 0;
    let mut v___x_3686_: usize = 0;
    let mut v___x_3687_: usize = 0;
    let mut v___x_3688_: usize = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3669_) == 0 {
                    return v_x_3668_;
                } else {
                    v_key_3670_ = leanh::lean_ctor_get(v_x_3669_, 0);
                    v_value_3671_ = leanh::lean_ctor_get(v_x_3669_, 1);
                    v_tail_3672_ = leanh::lean_ctor_get(v_x_3669_, 2);
                    v_isSharedCheck_3695_ = (!leanh::lean_is_exclusive(v_x_3669_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3674_ = v_x_3669_;
                        v_isShared_3675_ = v_isSharedCheck_3695_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3672_);
                        leanh::lean_inc(v_value_3671_);
                        leanh::lean_inc(v_key_3670_);
                        leanh::lean_dec(v_x_3669_);
                        v___x_3674_ = leanh::lean_box(0);
                        v_isShared_3675_ = v_isSharedCheck_3695_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3676_ = lean_array_get_size(v_x_3668_);
                v___x_3677_ = lean_uint64_of_nat(v_key_3670_);
                v___x_3678_ = 32u64;
                v___x_3679_ = lean_uint64_shift_right(v___x_3677_, v___x_3678_);
                v_fold_3680_ = lean_uint64_xor(v___x_3677_, v___x_3679_);
                v___x_3681_ = 16u64;
                v___x_3682_ = lean_uint64_shift_right(v_fold_3680_, v___x_3681_);
                v___x_3683_ = lean_uint64_xor(v_fold_3680_, v___x_3682_);
                v___x_3684_ = lean_uint64_to_usize(v___x_3683_);
                v___x_3685_ = lean_usize_of_nat(v___x_3676_);
                v___x_3686_ = 1usize;
                v___x_3687_ = lean_usize_sub(v___x_3685_, v___x_3686_);
                v___x_3688_ = lean_usize_land(v___x_3684_, v___x_3687_);
                v___x_3689_ = lean_array_uget_borrowed(v_x_3668_, v___x_3688_);
                leanh::lean_inc(v___x_3689_);
                if v_isShared_3675_ == 0 {
                    leanh::lean_ctor_set(v___x_3674_, 2, v___x_3689_);
                    v___x_3691_ = v___x_3674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_key_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_value_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 2, v___x_3689_);
                    v___x_3691_ = v_reuseFailAlloc_3694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3692_ = lean_array_uset(v_x_3668_, v___x_3688_, v___x_3691_);
                v_x_3668_ = v___x_3692_;
                v_x_3669_ = v_tail_3672_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(
    mut v_i_3696_: *mut leanh::LeanObject,
    mut v_source_3697_: *mut leanh::LeanObject,
    mut v_target_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u8 = 0;
    let mut v_es_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3699_ = lean_array_get_size(v_source_3697_);
                v___x_3700_ = lean_nat_dec_lt(v_i_3696_, v___x_3699_);
                if v___x_3700_ == 0 {
                    leanh::lean_dec_ref(v_source_3697_);
                    leanh::lean_dec(v_i_3696_);
                    return v_target_3698_;
                } else {
                    v_es_3701_ = lean_array_fget(v_source_3697_, v_i_3696_);
                    v___x_3702_ = leanh::lean_box(0);
                    v_source_3703_ = lean_array_fset(v_source_3697_, v_i_3696_, v___x_3702_);
                    v_target_3704_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(v_target_3698_, v_es_3701_);
                    v___x_3705_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3706_ = lean_nat_add(v_i_3696_, v___x_3705_);
                    leanh::lean_dec(v_i_3696_);
                    v_i_3696_ = v___x_3706_;
                    v_source_3697_ = v_source_3703_;
                    v_target_3698_ = v_target_3704_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(
    mut v_data_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3709_ = lean_array_get_size(v_data_3708_);
    v___x_3710_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3711_ = lean_nat_mul(v___x_3709_, v___x_3710_);
    v___x_3712_ = leanh::lean_unsigned_to_nat(0);
    v___x_3713_ = leanh::lean_box(0);
    v___x_3714_ = lean_mk_array(v_nbuckets_3711_, v___x_3713_);
    v___x_3715_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(v___x_3712_, v_data_3708_, v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(
    mut v_m_3716_: *mut leanh::LeanObject,
    mut v_a_3717_: *mut leanh::LeanObject,
    mut v_b_3718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: u64 = 0;
    let mut v___x_3726_: u64 = 0;
    let mut v___x_3727_: u64 = 0;
    let mut v_fold_3728_: u64 = 0;
    let mut v___x_3729_: u64 = 0;
    let mut v___x_3730_: u64 = 0;
    let mut v___x_3731_: u64 = 0;
    let mut v___x_3732_: usize = 0;
    let mut v___x_3733_: usize = 0;
    let mut v___x_3734_: usize = 0;
    let mut v___x_3735_: usize = 0;
    let mut v___x_3736_: usize = 0;
    let mut v_bkt_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut v_val_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3719_ = leanh::lean_ctor_get(v_m_3716_, 0);
                v_buckets_3720_ = leanh::lean_ctor_get(v_m_3716_, 1);
                v_isSharedCheck_3763_ = (!leanh::lean_is_exclusive(v_m_3716_)) as u8;
                if v_isSharedCheck_3763_ == 0 {
                    v___x_3722_ = v_m_3716_;
                    v_isShared_3723_ = v_isSharedCheck_3763_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3720_);
                    leanh::lean_inc(v_size_3719_);
                    leanh::lean_dec(v_m_3716_);
                    v___x_3722_ = leanh::lean_box(0);
                    v_isShared_3723_ = v_isSharedCheck_3763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3724_ = lean_array_get_size(v_buckets_3720_);
                v___x_3725_ = lean_uint64_of_nat(v_a_3717_);
                v___x_3726_ = 32u64;
                v___x_3727_ = lean_uint64_shift_right(v___x_3725_, v___x_3726_);
                v_fold_3728_ = lean_uint64_xor(v___x_3725_, v___x_3727_);
                v___x_3729_ = 16u64;
                v___x_3730_ = lean_uint64_shift_right(v_fold_3728_, v___x_3729_);
                v___x_3731_ = lean_uint64_xor(v_fold_3728_, v___x_3730_);
                v___x_3732_ = lean_uint64_to_usize(v___x_3731_);
                v___x_3733_ = lean_usize_of_nat(v___x_3724_);
                v___x_3734_ = 1usize;
                v___x_3735_ = lean_usize_sub(v___x_3733_, v___x_3734_);
                v___x_3736_ = lean_usize_land(v___x_3732_, v___x_3735_);
                v_bkt_3737_ = lean_array_uget_borrowed(v_buckets_3720_, v___x_3736_);
                v___x_3738_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_3717_, v_bkt_3737_);
                if v___x_3738_ == 0 {
                    v___x_3739_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3740_ = lean_nat_add(v_size_3719_, v___x_3739_);
                    leanh::lean_dec(v_size_3719_);
                    leanh::lean_inc(v_bkt_3737_);
                    v___x_3741_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3741_, 0, v_a_3717_);
                    leanh::lean_ctor_set(v___x_3741_, 1, v_b_3718_);
                    leanh::lean_ctor_set(v___x_3741_, 2, v_bkt_3737_);
                    v_buckets_x27_3742_ =
                        lean_array_uset(v_buckets_3720_, v___x_3736_, v___x_3741_);
                    v___x_3743_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3744_ = lean_nat_mul(v_size_x27_3740_, v___x_3743_);
                    v___x_3745_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3746_ = lean_nat_div(v___x_3744_, v___x_3745_);
                    leanh::lean_dec(v___x_3744_);
                    v___x_3747_ = lean_array_get_size(v_buckets_x27_3742_);
                    v___x_3748_ = lean_nat_dec_le(v___x_3746_, v___x_3747_);
                    leanh::lean_dec(v___x_3746_);
                    if v___x_3748_ == 0 {
                        v_val_3749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(v_buckets_x27_3742_);
                        if v_isShared_3723_ == 0 {
                            leanh::lean_ctor_set(v___x_3722_, 1, v_val_3749_);
                            leanh::lean_ctor_set(v___x_3722_, 0, v_size_x27_3740_);
                            v___x_3751_ = v___x_3722_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3752_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3752_,
                                0,
                                v_size_x27_3740_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_val_3749_);
                            v___x_3751_ = v_reuseFailAlloc_3752_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3723_ == 0 {
                            leanh::lean_ctor_set(v___x_3722_, 1, v_buckets_x27_3742_);
                            leanh::lean_ctor_set(v___x_3722_, 0, v_size_x27_3740_);
                            v___x_3754_ = v___x_3722_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3755_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3755_,
                                0,
                                v_size_x27_3740_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3755_,
                                1,
                                v_buckets_x27_3742_,
                            );
                            v___x_3754_ = v_reuseFailAlloc_3755_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3737_);
                    v___x_3756_ = leanh::lean_box(0);
                    v_buckets_x27_3757_ =
                        lean_array_uset(v_buckets_3720_, v___x_3736_, v___x_3756_);
                    v___x_3758_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_3717_, v_b_3718_, v_bkt_3737_);
                    v___x_3759_ = lean_array_uset(v_buckets_x27_3757_, v___x_3736_, v___x_3758_);
                    if v_isShared_3723_ == 0 {
                        leanh::lean_ctor_set(v___x_3722_, 1, v___x_3759_);
                        v___x_3761_ = v___x_3722_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_size_3719_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3762_, 1, v___x_3759_);
                        v___x_3761_ = v_reuseFailAlloc_3762_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3751_;
            }
            3 => {
                return v___x_3754_;
            }
            4 => {
                return v___x_3761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(
    mut v_aigSize_3764_: *mut leanh::LeanObject,
    mut v_assignment_3765_: *mut leanh::LeanObject,
    mut v_as_3766_: *mut leanh::LeanObject,
    mut v_sz_3767_: usize,
    mut v_i_3768_: usize,
    mut v_b_3769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3770_: u8 = 0;
    let mut v_a_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: u8 = 0;
    let mut v_var_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: usize = 0;
    let mut v___x_3784_: usize = 0;
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3770_ = lean_usize_dec_lt(v_i_3768_, v_sz_3767_);
                if v___x_3770_ == 0 {
                    return v_b_3769_;
                } else {
                    v_a_3771_ = lean_array_uget_borrowed(v_as_3766_, v_i_3768_);
                    v_fst_3772_ = leanh::lean_ctor_get(v_a_3771_, 0);
                    v_snd_3773_ = leanh::lean_ctor_get(v_a_3771_, 1);
                    v___x_3786_ = lean_nat_add(v_snd_3773_, v_aigSize_3764_);
                    v___x_3787_ = lean_array_get_size(v_assignment_3765_);
                    v___x_3788_ = lean_nat_dec_lt(v___x_3786_, v___x_3787_);
                    if v___x_3788_ == 0 {
                        leanh::lean_dec(v___x_3786_);
                        v___y_3775_ = v___x_3770_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3789_ = lean_array_fget_borrowed(v_assignment_3765_, v___x_3786_);
                        leanh::lean_dec(v___x_3786_);
                        v_fst_3790_ = leanh::lean_ctor_get(v___x_3789_, 0);
                        v___x_3791_ = (leanh::lean_unbox(v_fst_3790_) as u8);
                        v___y_3775_ = v___x_3791_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_var_3776_ = leanh::lean_ctor_get(v_fst_3772_, 0);
                v_idx_3777_ = leanh::lean_ctor_get(v_fst_3772_, 2);
                v___x_3778_ = leanh::lean_box(1);
                v___x_3779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_b_3769_, v_var_3776_, v___x_3778_);
                v___x_3780_ = leanh::lean_box((v___y_3775_) as usize);
                leanh::lean_inc(v_idx_3777_);
                v___x_3781_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_idx_3777_, v___x_3780_, v___x_3779_);
                leanh::lean_inc(v_var_3776_);
                v___x_3782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_b_3769_, v_var_3776_, v___x_3781_);
                v___x_3783_ = 1usize;
                v___x_3784_ = lean_usize_add(v_i_3768_, v___x_3783_);
                v_i_3768_ = v___x_3784_;
                v_b_3769_ = v___x_3782_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7___boxed(
    mut v_aigSize_3792_: *mut leanh::LeanObject,
    mut v_assignment_3793_: *mut leanh::LeanObject,
    mut v_as_3794_: *mut leanh::LeanObject,
    mut v_sz_3795_: *mut leanh::LeanObject,
    mut v_i_3796_: *mut leanh::LeanObject,
    mut v_b_3797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3798_: usize = 0;
    let mut v_i_boxed_3799_: usize = 0;
    let mut v_res_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3798_ = leanh::lean_unbox_usize(v_sz_3795_);
    leanh::lean_dec(v_sz_3795_);
    v_i_boxed_3799_ = leanh::lean_unbox_usize(v_i_3796_);
    leanh::lean_dec(v_i_3796_);
    v_res_3800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_aigSize_3792_, v_assignment_3793_, v_as_3794_, v_sz_boxed_3798_, v_i_boxed_3799_, v_b_3797_);
    leanh::lean_dec_ref(v_as_3794_);
    leanh::lean_dec_ref(v_assignment_3793_);
    leanh::lean_dec(v_aigSize_3792_);
    return v_res_3800_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(
    mut v_x_3801_: *mut leanh::LeanObject,
    mut v_x_3802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3802_) == 0 {
                    return v_x_3801_;
                } else {
                    v_key_3803_ = leanh::lean_ctor_get(v_x_3802_, 0);
                    v_value_3804_ = leanh::lean_ctor_get(v_x_3802_, 1);
                    v_tail_3805_ = leanh::lean_ctor_get(v_x_3802_, 2);
                    leanh::lean_inc(v_value_3804_);
                    leanh::lean_inc(v_key_3803_);
                    v___x_3806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3806_, 0, v_key_3803_);
                    leanh::lean_ctor_set(v___x_3806_, 1, v_value_3804_);
                    v___x_3807_ = lean_array_push(v_x_3801_, v___x_3806_);
                    v_x_3801_ = v___x_3807_;
                    v_x_3802_ = v_tail_3805_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9___boxed(
    mut v_x_3809_: *mut leanh::LeanObject,
    mut v_x_3810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3811_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_x_3809_, v_x_3810_);
    leanh::lean_dec(v_x_3810_);
    return v_res_3811_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(
    mut v_as_3812_: *mut leanh::LeanObject,
    mut v_i_3813_: usize,
    mut v_stop_3814_: usize,
    mut v_b_3815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: usize = 0;
    let mut v___x_3820_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3816_ = lean_usize_dec_eq(v_i_3813_, v_stop_3814_);
                if v___x_3816_ == 0 {
                    v___x_3817_ = lean_array_uget_borrowed(v_as_3812_, v_i_3813_);
                    v___x_3818_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__9(v_b_3815_, v___x_3817_);
                    v___x_3819_ = 1usize;
                    v___x_3820_ = lean_usize_add(v_i_3813_, v___x_3819_);
                    v_i_3813_ = v___x_3820_;
                    v_b_3815_ = v___x_3818_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3815_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10___boxed(
    mut v_as_3822_: *mut leanh::LeanObject,
    mut v_i_3823_: *mut leanh::LeanObject,
    mut v_stop_3824_: *mut leanh::LeanObject,
    mut v_b_3825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3826_: usize = 0;
    let mut v_stop_boxed_3827_: usize = 0;
    let mut v_res_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3826_ = leanh::lean_unbox_usize(v_i_3823_);
    leanh::lean_dec(v_i_3823_);
    v_stop_boxed_3827_ = leanh::lean_unbox_usize(v_stop_3824_);
    leanh::lean_dec(v_stop_3824_);
    v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_as_3822_, v_i_boxed_3826_, v_stop_boxed_3827_, v_b_3825_);
    leanh::lean_dec_ref(v_as_3822_);
    return v_res_3828_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(
    mut v_x_3829_: *mut leanh::LeanObject,
    mut v_x_3830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3830_) == 0 {
                    return v_x_3829_;
                } else {
                    v_key_3831_ = leanh::lean_ctor_get(v_x_3830_, 0);
                    v_value_3832_ = leanh::lean_ctor_get(v_x_3830_, 1);
                    v_tail_3833_ = leanh::lean_ctor_get(v_x_3830_, 2);
                    leanh::lean_inc(v_value_3832_);
                    leanh::lean_inc(v_key_3831_);
                    v___x_3834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3834_, 0, v_key_3831_);
                    leanh::lean_ctor_set(v___x_3834_, 1, v_value_3832_);
                    v___x_3835_ = lean_array_push(v_x_3829_, v___x_3834_);
                    v_x_3829_ = v___x_3835_;
                    v_x_3830_ = v_tail_3833_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12___boxed(
    mut v_x_3837_: *mut leanh::LeanObject,
    mut v_x_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_x_3837_, v_x_3838_);
    leanh::lean_dec(v_x_3838_);
    return v_res_3839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(
    mut v_as_3840_: *mut leanh::LeanObject,
    mut v_i_3841_: usize,
    mut v_stop_3842_: usize,
    mut v_b_3843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: usize = 0;
    let mut v___x_3848_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3844_ = lean_usize_dec_eq(v_i_3841_, v_stop_3842_);
                if v___x_3844_ == 0 {
                    v___x_3845_ = lean_array_uget_borrowed(v_as_3840_, v_i_3841_);
                    v___x_3846_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__12(v_b_3843_, v___x_3845_);
                    v___x_3847_ = 1usize;
                    v___x_3848_ = lean_usize_add(v_i_3841_, v___x_3847_);
                    v_i_3841_ = v___x_3848_;
                    v_b_3843_ = v___x_3846_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3843_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13___boxed(
    mut v_as_3850_: *mut leanh::LeanObject,
    mut v_i_3851_: *mut leanh::LeanObject,
    mut v_stop_3852_: *mut leanh::LeanObject,
    mut v_b_3853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3854_: usize = 0;
    let mut v_stop_boxed_3855_: usize = 0;
    let mut v_res_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3854_ = leanh::lean_unbox_usize(v_i_3851_);
    leanh::lean_dec(v_i_3851_);
    v_stop_boxed_3855_ = leanh::lean_unbox_usize(v_stop_3852_);
    leanh::lean_dec(v_stop_3852_);
    v_res_3856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_as_3850_, v_i_boxed_3854_, v_stop_boxed_3855_, v_b_3853_);
    leanh::lean_dec_ref(v_as_3850_);
    return v_res_3856_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(
    mut v_as_3857_: *mut leanh::LeanObject,
    mut v_i_3858_: usize,
    mut v_stop_3859_: usize,
    mut v_b_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3861_: u8 = 0;
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: usize = 0;
    let mut v___x_3866_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3861_ = lean_usize_dec_eq(v_i_3858_, v_stop_3859_);
                if v___x_3861_ == 0 {
                    v___x_3862_ = lean_array_uget_borrowed(v_as_3857_, v_i_3858_);
                    v___x_3863_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_3862_);
                    v___x_3864_ = lean_nat_add(v_b_3860_, v___x_3863_);
                    leanh::lean_dec(v___x_3863_);
                    leanh::lean_dec(v_b_3860_);
                    v___x_3865_ = 1usize;
                    v___x_3866_ = lean_usize_add(v_i_3858_, v___x_3865_);
                    v_i_3858_ = v___x_3866_;
                    v_b_3860_ = v___x_3864_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3860_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18___boxed(
    mut v_as_3868_: *mut leanh::LeanObject,
    mut v_i_3869_: *mut leanh::LeanObject,
    mut v_stop_3870_: *mut leanh::LeanObject,
    mut v_b_3871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3872_: usize = 0;
    let mut v_stop_boxed_3873_: usize = 0;
    let mut v_res_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3872_ = leanh::lean_unbox_usize(v_i_3869_);
    leanh::lean_dec(v_i_3869_);
    v_stop_boxed_3873_ = leanh::lean_unbox_usize(v_stop_3870_);
    leanh::lean_dec(v_stop_3870_);
    v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_as_3868_, v_i_boxed_3872_, v_stop_boxed_3873_, v_b_3871_);
    leanh::lean_dec_ref(v_as_3868_);
    return v_res_3874_;
}
pub unsafe fn _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ = 0;
    v___x_3876_ = l_Lean_instInhabitedExpr;
    v___x_3877_ = leanh::lean_box((v___x_3875_) as usize);
    v___x_3878_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3878_, 0, v___x_3876_);
    leanh::lean_ctor_set(v___x_3878_, 1, v___x_3877_);
    return v___x_3878_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(
    mut v_msg_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3880_ = leanh::lean_unsigned_to_nat(0);
    v___x_3881_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0_once), _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2___closed__0);
    v___x_3882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3882_, 0, v___x_3880_);
    leanh::lean_ctor_set(v___x_3882_, 1, v___x_3881_);
    v___x_3883_ = lean_panic_fn_borrowed(v___x_3882_, v_msg_3879_);
    leanh::lean_dec_ref_known(v___x_3882_, 2);
    return v___x_3883_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__2;
    v___x_3888_ = leanh::lean_unsigned_to_nat(11);
    v___x_3889_ = leanh::lean_unsigned_to_nat(163);
    v___x_3890_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__1;
    v___x_3891_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__0;
    v___x_3892_ = l_mkPanicMessageWithDecl(
        v___x_3891_,
        v___x_3890_,
        v___x_3889_,
        v___x_3888_,
        v___x_3887_,
    );
    return v___x_3892_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(
    mut v_a_3893_: *mut leanh::LeanObject,
    mut v_x_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3894_) == 0 {
                    v___x_3895_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___closed__3);
                    v___x_3896_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1_spec__2(v___x_3895_);
                    return v___x_3896_;
                } else {
                    v_key_3897_ = leanh::lean_ctor_get(v_x_3894_, 0);
                    v_value_3898_ = leanh::lean_ctor_get(v_x_3894_, 1);
                    v_tail_3899_ = leanh::lean_ctor_get(v_x_3894_, 2);
                    v___x_3900_ = lean_nat_dec_eq(v_key_3897_, v_a_3893_);
                    if v___x_3900_ == 0 {
                        v_x_3894_ = v_tail_3899_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3898_);
                        return v_value_3898_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1___boxed(
    mut v_a_3902_: *mut leanh::LeanObject,
    mut v_x_3903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_a_3902_, v_x_3903_);
    leanh::lean_dec(v_x_3903_);
    leanh::lean_dec(v_a_3902_);
    return v_res_3904_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(
    mut v_m_3905_: *mut leanh::LeanObject,
    mut v_a_3906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u64 = 0;
    let mut v___x_3910_: u64 = 0;
    let mut v___x_3911_: u64 = 0;
    let mut v_fold_3912_: u64 = 0;
    let mut v___x_3913_: u64 = 0;
    let mut v___x_3914_: u64 = 0;
    let mut v___x_3915_: u64 = 0;
    let mut v___x_3916_: usize = 0;
    let mut v___x_3917_: usize = 0;
    let mut v___x_3918_: usize = 0;
    let mut v___x_3919_: usize = 0;
    let mut v___x_3920_: usize = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3907_ = leanh::lean_ctor_get(v_m_3905_, 1);
    v___x_3908_ = lean_array_get_size(v_buckets_3907_);
    v___x_3909_ = lean_uint64_of_nat(v_a_3906_);
    v___x_3910_ = 32u64;
    v___x_3911_ = lean_uint64_shift_right(v___x_3909_, v___x_3910_);
    v_fold_3912_ = lean_uint64_xor(v___x_3909_, v___x_3911_);
    v___x_3913_ = 16u64;
    v___x_3914_ = lean_uint64_shift_right(v_fold_3912_, v___x_3913_);
    v___x_3915_ = lean_uint64_xor(v_fold_3912_, v___x_3914_);
    v___x_3916_ = lean_uint64_to_usize(v___x_3915_);
    v___x_3917_ = lean_usize_of_nat(v___x_3908_);
    v___x_3918_ = 1usize;
    v___x_3919_ = lean_usize_sub(v___x_3917_, v___x_3918_);
    v___x_3920_ = lean_usize_land(v___x_3916_, v___x_3919_);
    v___x_3921_ = lean_array_uget_borrowed(v_buckets_3907_, v___x_3920_);
    v___x_3922_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1_spec__1(v_a_3906_, v___x_3921_);
    return v___x_3922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1___boxed(
    mut v_m_3923_: *mut leanh::LeanObject,
    mut v_a_3924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_m_3923_, v_a_3924_);
    leanh::lean_dec(v_a_3924_);
    leanh::lean_dec_ref(v_m_3923_);
    return v_res_3925_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(
    mut v_atomsAssignment_3926_: *mut leanh::LeanObject,
    mut v_acc_3927_: *mut leanh::LeanObject,
    mut v_a_3928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3934_: u8 = 0;
    let mut v_var_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3928_) == 0 {
                    return v_acc_3927_;
                } else {
                    v_key_3929_ = leanh::lean_ctor_get(v_a_3928_, 0);
                    v_value_3930_ = leanh::lean_ctor_get(v_a_3928_, 1);
                    v_tail_3931_ = leanh::lean_ctor_get(v_a_3928_, 2);
                    v_isSharedCheck_3945_ = (!leanh::lean_is_exclusive(v_a_3928_)) as u8;
                    if v_isSharedCheck_3945_ == 0 {
                        v___x_3933_ = v_a_3928_;
                        v_isShared_3934_ = v_isSharedCheck_3945_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3931_);
                        leanh::lean_inc(v_value_3930_);
                        leanh::lean_inc(v_key_3929_);
                        leanh::lean_dec(v_a_3928_);
                        v___x_3933_ = leanh::lean_box(0);
                        v_isShared_3934_ = v_isSharedCheck_3945_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_var_3935_ = leanh::lean_ctor_get(v_key_3929_, 0);
                v___x_3936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_3926_, v_var_3935_);
                v_snd_3937_ = leanh::lean_ctor_get(v___x_3936_, 1);
                leanh::lean_inc(v_snd_3937_);
                leanh::lean_dec_ref(v___x_3936_);
                v_snd_3938_ = leanh::lean_ctor_get(v_snd_3937_, 1);
                leanh::lean_inc(v_snd_3938_);
                leanh::lean_dec(v_snd_3937_);
                v___x_3939_ = (leanh::lean_unbox(v_snd_3938_) as u8);
                leanh::lean_dec(v_snd_3938_);
                if v___x_3939_ == 0 {
                    if v_isShared_3934_ == 0 {
                        leanh::lean_ctor_set(v___x_3933_, 2, v_acc_3927_);
                        v___x_3941_ = v___x_3933_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3943_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_key_3929_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_value_3930_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_acc_3927_);
                        v___x_3941_ = v_reuseFailAlloc_3943_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3933_);
                    leanh::lean_dec(v_value_3930_);
                    leanh::lean_dec(v_key_3929_);
                    v_a_3928_ = v_tail_3931_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_acc_3927_ = v___x_3941_;
                v_a_3928_ = v_tail_3931_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16___boxed(
    mut v_atomsAssignment_3946_: *mut leanh::LeanObject,
    mut v_acc_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3949_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(v_atomsAssignment_3946_, v_acc_3947_, v_a_3948_);
    leanh::lean_dec_ref(v_atomsAssignment_3946_);
    return v_res_3949_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(
    mut v_atomsAssignment_3950_: *mut leanh::LeanObject,
    mut v_sz_3951_: usize,
    mut v_i_3952_: usize,
    mut v_bs_3953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3954_: u8 = 0;
    let mut v_v_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: usize = 0;
    let mut v___x_3961_: usize = 0;
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3954_ = lean_usize_dec_lt(v_i_3952_, v_sz_3951_);
                if v___x_3954_ == 0 {
                    return v_bs_3953_;
                } else {
                    v_v_3955_ = lean_array_uget(v_bs_3953_, v_i_3952_);
                    v___x_3956_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3957_ = lean_array_uset(v_bs_3953_, v_i_3952_, v___x_3956_);
                    v___x_3958_ = leanh::lean_box(0);
                    v___x_3959_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__16(v_atomsAssignment_3950_, v___x_3958_, v_v_3955_);
                    v___x_3960_ = 1usize;
                    v___x_3961_ = lean_usize_add(v_i_3952_, v___x_3960_);
                    v___x_3962_ = lean_array_uset(v_bs_x27_3957_, v_i_3952_, v___x_3959_);
                    v_i_3952_ = v___x_3961_;
                    v_bs_3953_ = v___x_3962_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17___boxed(
    mut v_atomsAssignment_3964_: *mut leanh::LeanObject,
    mut v_sz_3965_: *mut leanh::LeanObject,
    mut v_i_3966_: *mut leanh::LeanObject,
    mut v_bs_3967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3968_: usize = 0;
    let mut v_i_boxed_3969_: usize = 0;
    let mut v_res_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3968_ = leanh::lean_unbox_usize(v_sz_3965_);
    leanh::lean_dec(v_sz_3965_);
    v_i_boxed_3969_ = leanh::lean_unbox_usize(v_i_3966_);
    leanh::lean_dec(v_i_3966_);
    v_res_3970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_atomsAssignment_3964_, v_sz_boxed_3968_, v_i_boxed_3969_, v_bs_3967_);
    leanh::lean_dec_ref(v_atomsAssignment_3964_);
    return v_res_3970_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(
    mut v_atomsAssignment_3971_: *mut leanh::LeanObject,
    mut v_m_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v_sz_3977_: usize = 0;
    let mut v___x_3978_: usize = 0;
    let mut v_newBuckets_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: usize = 0;
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_unused_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3973_ = leanh::lean_ctor_get(v_m_3972_, 1);
                v_isSharedCheck_4000_ = (!leanh::lean_is_exclusive(v_m_3972_)) as u8;
                if v_isSharedCheck_4000_ == 0 {
                    v_unused_4001_ = leanh::lean_ctor_get(v_m_3972_, 0);
                    leanh::lean_dec(v_unused_4001_);
                    v___x_3975_ = v_m_3972_;
                    v_isShared_3976_ = v_isSharedCheck_4000_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3973_);
                    leanh::lean_dec(v_m_3972_);
                    v___x_3975_ = leanh::lean_box(0);
                    v_isShared_3976_ = v_isSharedCheck_4000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_3977_ = lean_array_size(v_buckets_3973_);
                v___x_3978_ = 0usize;
                v_newBuckets_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__17(v_atomsAssignment_3971_, v_sz_3977_, v___x_3978_, v_buckets_3973_);
                v___x_3980_ = leanh::lean_unsigned_to_nat(0);
                v___x_3981_ = lean_array_get_size(v_newBuckets_3979_);
                v___x_3982_ = lean_nat_dec_lt(v___x_3980_, v___x_3981_);
                if v___x_3982_ == 0 {
                    if v_isShared_3976_ == 0 {
                        leanh::lean_ctor_set(v___x_3975_, 1, v_newBuckets_3979_);
                        leanh::lean_ctor_set(v___x_3975_, 0, v___x_3980_);
                        v___x_3984_ = v___x_3975_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3985_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3980_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_newBuckets_3979_);
                        v___x_3984_ = v_reuseFailAlloc_3985_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3986_ = lean_nat_dec_le(v___x_3981_, v___x_3981_);
                    if v___x_3986_ == 0 {
                        if v___x_3982_ == 0 {
                            if v_isShared_3976_ == 0 {
                                leanh::lean_ctor_set(v___x_3975_, 1, v_newBuckets_3979_);
                                leanh::lean_ctor_set(v___x_3975_, 0, v___x_3980_);
                                v___x_3988_ = v___x_3975_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3989_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3980_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3989_,
                                    1,
                                    v_newBuckets_3979_,
                                );
                                v___x_3988_ = v_reuseFailAlloc_3989_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_3990_ = lean_usize_of_nat(v___x_3981_);
                            v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_newBuckets_3979_, v___x_3978_, v___x_3990_, v___x_3980_);
                            if v_isShared_3976_ == 0 {
                                leanh::lean_ctor_set(v___x_3975_, 1, v_newBuckets_3979_);
                                leanh::lean_ctor_set(v___x_3975_, 0, v___x_3991_);
                                v___x_3993_ = v___x_3975_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3994_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3991_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3994_,
                                    1,
                                    v_newBuckets_3979_,
                                );
                                v___x_3993_ = v_reuseFailAlloc_3994_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_3995_ = lean_usize_of_nat(v___x_3981_);
                        v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11_spec__18(v_newBuckets_3979_, v___x_3978_, v___x_3995_, v___x_3980_);
                        if v_isShared_3976_ == 0 {
                            leanh::lean_ctor_set(v___x_3975_, 1, v_newBuckets_3979_);
                            leanh::lean_ctor_set(v___x_3975_, 0, v___x_3996_);
                            v___x_3998_ = v___x_3975_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3999_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3999_,
                                1,
                                v_newBuckets_3979_,
                            );
                            v___x_3998_ = v_reuseFailAlloc_3999_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3984_;
            }
            3 => {
                return v___x_3988_;
            }
            4 => {
                return v___x_3993_;
            }
            5 => {
                return v___x_3998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11___boxed(
    mut v_atomsAssignment_4002_: *mut leanh::LeanObject,
    mut v_m_4003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_atomsAssignment_4002_, v_m_4003_);
    leanh::lean_dec_ref(v_atomsAssignment_4002_);
    return v_res_4004_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__2;
    v___x_4009_ = leanh::lean_unsigned_to_nat(6);
    v___x_4010_ = leanh::lean_unsigned_to_nat(69);
    v___x_4011_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__1;
    v___x_4012_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0;
    v___x_4013_ = l_mkPanicMessageWithDecl(
        v___x_4012_,
        v___x_4011_,
        v___x_4010_,
        v___x_4009_,
        v___x_4008_,
    );
    return v___x_4013_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(
    mut v_as_x27_4014_: *mut leanh::LeanObject,
    mut v_b_4015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4024_: u8 = 0;
    let mut v_value_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_4014_) == 0 {
                    return v_b_4015_;
                } else {
                    v_head_4016_ = leanh::lean_ctor_get(v_as_x27_4014_, 0);
                    v_tail_4017_ = leanh::lean_ctor_get(v_as_x27_4014_, 1);
                    v_fst_4018_ = leanh::lean_ctor_get(v_head_4016_, 0);
                    v_snd_4019_ = leanh::lean_ctor_get(v_head_4016_, 1);
                    v_fst_4020_ = leanh::lean_ctor_get(v_b_4015_, 0);
                    v_snd_4021_ = leanh::lean_ctor_get(v_b_4015_, 1);
                    v_isSharedCheck_4043_ = (!leanh::lean_is_exclusive(v_b_4015_)) as u8;
                    if v_isSharedCheck_4043_ == 0 {
                        v___x_4023_ = v_b_4015_;
                        v_isShared_4024_ = v_isSharedCheck_4043_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4021_);
                        leanh::lean_inc(v_fst_4020_);
                        leanh::lean_dec(v_b_4015_);
                        v___x_4023_ = leanh::lean_box(0);
                        v_isShared_4024_ = v_isSharedCheck_4043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4033_ = lean_nat_dec_eq(v_fst_4018_, v_snd_4021_);
                if v___x_4033_ == 0 {
                    leanh::lean_del_object(v___x_4023_);
                    leanh::lean_dec(v_snd_4021_);
                    leanh::lean_dec(v_fst_4020_);
                    v___x_4034_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__3);
                    v___x_4035_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__0(v___x_4034_);
                    if leanh::lean_obj_tag(v___x_4035_) == 0 {
                        v_a_4036_ = leanh::lean_ctor_get(v___x_4035_, 0);
                        leanh::lean_inc(v_a_4036_);
                        leanh::lean_dec_ref_known(v___x_4035_, 1);
                        return v_a_4036_;
                    } else {
                        v_a_4037_ = leanh::lean_ctor_get(v___x_4035_, 0);
                        leanh::lean_inc(v_a_4037_);
                        leanh::lean_dec_ref_known(v___x_4035_, 1);
                        v_as_x27_4014_ = v_tail_4017_;
                        v_b_4015_ = v_a_4037_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_4039_ = (leanh::lean_unbox(v_snd_4019_) as u8);
                    if v___x_4039_ == 0 {
                        v_value_4026_ = v_fst_4020_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4040_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4041_ = lean_nat_shiftl(v___x_4040_, v_snd_4021_);
                        v___x_4042_ = lean_nat_lor(v_fst_4020_, v___x_4041_);
                        leanh::lean_dec(v___x_4041_);
                        leanh::lean_dec(v_fst_4020_);
                        v_value_4026_ = v___x_4042_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4027_ = leanh::lean_unsigned_to_nat(1);
                v___x_4028_ = lean_nat_add(v_snd_4021_, v___x_4027_);
                leanh::lean_dec(v_snd_4021_);
                if v_isShared_4024_ == 0 {
                    leanh::lean_ctor_set(v___x_4023_, 1, v___x_4028_);
                    leanh::lean_ctor_set(v___x_4023_, 0, v_value_4026_);
                    v___x_4030_ = v___x_4023_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_value_4026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 1, v___x_4028_);
                    v___x_4030_ = v_reuseFailAlloc_4032_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_as_x27_4014_ = v_tail_4017_;
                v_b_4015_ = v___x_4030_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___boxed(
    mut v_as_x27_4044_: *mut leanh::LeanObject,
    mut v_b_4045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_4044_, v_b_4045_);
    leanh::lean_dec(v_as_x27_4044_);
    return v_res_4046_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(
    mut v_init_4047_: *mut leanh::LeanObject,
    mut v_x_4048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4048_) == 0 {
                    v_k_4049_ = leanh::lean_ctor_get(v_x_4048_, 1);
                    v_v_4050_ = leanh::lean_ctor_get(v_x_4048_, 2);
                    v_l_4051_ = leanh::lean_ctor_get(v_x_4048_, 3);
                    v_r_4052_ = leanh::lean_ctor_get(v_x_4048_, 4);
                    v___x_4053_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_4047_, v_r_4052_);
                    leanh::lean_inc(v_v_4050_);
                    leanh::lean_inc(v_k_4049_);
                    v___x_4054_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4054_, 0, v_k_4049_);
                    leanh::lean_ctor_set(v___x_4054_, 1, v_v_4050_);
                    v___x_4055_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4055_, 0, v___x_4054_);
                    leanh::lean_ctor_set(v___x_4055_, 1, v___x_4053_);
                    v_init_4047_ = v___x_4055_;
                    v_x_4048_ = v_l_4051_;
                    state = 0;
                    continue;
                } else {
                    return v_init_4047_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2___boxed(
    mut v_init_4057_: *mut leanh::LeanObject,
    mut v_x_4058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4059_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v_init_4057_, v_x_4058_);
    leanh::lean_dec(v_x_4058_);
    return v_res_4059_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(
    mut v_atomsAssignment_4062_: *mut leanh::LeanObject,
    mut v_as_4063_: *mut leanh::LeanObject,
    mut v_sz_4064_: usize,
    mut v_i_4065_: usize,
    mut v_b_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4067_: u8 = 0;
    let mut v_a_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4085_: u8 = 0;
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: usize = 0;
    let mut v___x_4093_: usize = 0;
    let mut v_reuseFailAlloc_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_unused_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4067_ = lean_usize_dec_lt(v_i_4065_, v_sz_4064_);
                if v___x_4067_ == 0 {
                    return v_b_4066_;
                } else {
                    v_a_4068_ = lean_array_uget_borrowed(v_as_4063_, v_i_4065_);
                    v_fst_4069_ = leanh::lean_ctor_get(v_a_4068_, 0);
                    v_snd_4070_ = leanh::lean_ctor_get(v_a_4068_, 1);
                    v___x_4071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___closed__0;
                    v___x_4072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__1(v_atomsAssignment_4062_, v_fst_4069_);
                    v_snd_4073_ = leanh::lean_ctor_get(v___x_4072_, 1);
                    leanh::lean_inc(v_snd_4073_);
                    leanh::lean_dec_ref(v___x_4072_);
                    v_fst_4074_ = leanh::lean_ctor_get(v_snd_4073_, 0);
                    v_isSharedCheck_4098_ = (!leanh::lean_is_exclusive(v_snd_4073_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v_unused_4099_ = leanh::lean_ctor_get(v_snd_4073_, 1);
                        leanh::lean_dec(v_unused_4099_);
                        v___x_4076_ = v_snd_4073_;
                        v_isShared_4077_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_4074_);
                        leanh::lean_dec(v_snd_4073_);
                        v___x_4076_ = leanh::lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4078_ = leanh::lean_box(0);
                v___x_4079_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__2(v___x_4078_, v_snd_4070_);
                v___x_4080_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v___x_4079_, v___x_4071_);
                leanh::lean_dec(v___x_4079_);
                v_fst_4081_ = leanh::lean_ctor_get(v___x_4080_, 0);
                v_snd_4082_ = leanh::lean_ctor_get(v___x_4080_, 1);
                v_isSharedCheck_4097_ = (!leanh::lean_is_exclusive(v___x_4080_)) as u8;
                if v_isSharedCheck_4097_ == 0 {
                    v___x_4084_ = v___x_4080_;
                    v_isShared_4085_ = v_isSharedCheck_4097_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4082_);
                    leanh::lean_inc(v_fst_4081_);
                    leanh::lean_dec(v___x_4080_);
                    v___x_4084_ = leanh::lean_box(0);
                    v_isShared_4085_ = v_isSharedCheck_4097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4086_ = l_BitVec_ofNat(v_snd_4082_, v_fst_4081_);
                leanh::lean_dec(v_fst_4081_);
                if v_isShared_4077_ == 0 {
                    leanh::lean_ctor_set(v___x_4076_, 1, v___x_4086_);
                    leanh::lean_ctor_set(v___x_4076_, 0, v_snd_4082_);
                    v___x_4088_ = v___x_4076_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_snd_4082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4086_);
                    v___x_4088_ = v_reuseFailAlloc_4096_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4085_ == 0 {
                    leanh::lean_ctor_set(v___x_4084_, 1, v___x_4088_);
                    leanh::lean_ctor_set(v___x_4084_, 0, v_fst_4074_);
                    v___x_4090_ = v___x_4084_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_fst_4074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4088_);
                    v___x_4090_ = v_reuseFailAlloc_4095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4091_ = lean_array_push(v_b_4066_, v___x_4090_);
                v___x_4092_ = 1usize;
                v___x_4093_ = lean_usize_add(v_i_4065_, v___x_4092_);
                v_i_4065_ = v___x_4093_;
                v_b_4066_ = v___x_4091_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8___boxed(
    mut v_atomsAssignment_4100_: *mut leanh::LeanObject,
    mut v_as_4101_: *mut leanh::LeanObject,
    mut v_sz_4102_: *mut leanh::LeanObject,
    mut v_i_4103_: *mut leanh::LeanObject,
    mut v_b_4104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4105_: usize = 0;
    let mut v_i_boxed_4106_: usize = 0;
    let mut v_res_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4105_ = leanh::lean_unbox_usize(v_sz_4102_);
    leanh::lean_dec(v_sz_4102_);
    v_i_boxed_4106_ = leanh::lean_unbox_usize(v_i_4103_);
    leanh::lean_dec(v_i_4103_);
    v_res_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_4100_, v_as_4101_, v_sz_boxed_4105_, v_i_boxed_4106_, v_b_4104_);
    leanh::lean_dec_ref(v_as_4101_);
    leanh::lean_dec_ref(v_atomsAssignment_4100_);
    return v_res_4107_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4108_ = leanh::lean_box(0);
    v___x_4109_ = leanh::lean_unsigned_to_nat(16);
    v___x_4110_ = lean_mk_array(v___x_4109_, v___x_4108_);
    return v___x_4110_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sparseMap_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__0,
    );
    v___x_4112_ = leanh::lean_unsigned_to_nat(0);
    v_sparseMap_4113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_sparseMap_4113_, 0, v___x_4112_);
    leanh::lean_ctor_set(v_sparseMap_4113_, 1, v___x_4111_);
    return v_sparseMap_4113_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(
    mut v_var2Cnf_4116_: *mut leanh::LeanObject,
    mut v_assignment_4117_: *mut leanh::LeanObject,
    mut v_aigSize_4118_: *mut leanh::LeanObject,
    mut v_atomsAssignment_4119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4122_: usize = 0;
    let mut v___y_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4124_: usize = 0;
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sparseMap_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4133_: usize = 0;
    let mut v___x_4134_: usize = 0;
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: usize = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4150_: u8 = 0;
    let mut v___x_4151_: usize = 0;
    let mut v___x_4152_: usize = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: usize = 0;
    let mut v___x_4155_: usize = 0;
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4126_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__11(v_atomsAssignment_4119_, v_var2Cnf_4116_);
                v_size_4127_ = leanh::lean_ctor_get(v___x_4126_, 0);
                leanh::lean_inc(v_size_4127_);
                v_buckets_4128_ = leanh::lean_ctor_get(v___x_4126_, 1);
                leanh::lean_inc_ref(v_buckets_4128_);
                leanh::lean_dec_ref(v___x_4126_);
                v___x_4129_ = leanh::lean_unsigned_to_nat(0);
                v_sparseMap_4130_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__1,
                );
                v___x_4147_ = lean_mk_empty_array_with_capacity(v_size_4127_);
                leanh::lean_dec(v_size_4127_);
                v___x_4148_ = lean_array_get_size(v_buckets_4128_);
                v___x_4149_ = lean_nat_dec_lt(v___x_4129_, v___x_4148_);
                if v___x_4149_ == 0 {
                    leanh::lean_dec_ref(v_buckets_4128_);
                    v___y_4132_ = v___x_4147_;
                    state = 2;
                    continue;
                } else {
                    v___x_4150_ = lean_nat_dec_le(v___x_4148_, v___x_4148_);
                    if v___x_4150_ == 0 {
                        if v___x_4149_ == 0 {
                            leanh::lean_dec_ref(v_buckets_4128_);
                            v___y_4132_ = v___x_4147_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4151_ = 0usize;
                            v___x_4152_ = lean_usize_of_nat(v___x_4148_);
                            v___x_4153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_buckets_4128_, v___x_4151_, v___x_4152_, v___x_4147_);
                            leanh::lean_dec_ref(v_buckets_4128_);
                            v___y_4132_ = v___x_4153_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_4154_ = 0usize;
                        v___x_4155_ = lean_usize_of_nat(v___x_4148_);
                        v___x_4156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__13(v_buckets_4128_, v___x_4154_, v___x_4155_, v___x_4147_);
                        leanh::lean_dec_ref(v_buckets_4128_);
                        v___y_4132_ = v___x_4156_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_4124_ = lean_array_size(v___y_4123_);
                leanh::lean_inc_ref(v___y_4121_);
                v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__8(v_atomsAssignment_4119_, v___y_4123_, v_sz_4124_, v___y_4122_, v___y_4121_);
                leanh::lean_dec_ref(v___y_4123_);
                return v___x_4125_;
            }
            2 => {
                v_sz_4133_ = lean_array_size(v___y_4132_);
                v___x_4134_ = 0usize;
                v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__7(v_aigSize_4118_, v_assignment_4117_, v___y_4132_, v_sz_4133_, v___x_4134_, v_sparseMap_4130_);
                leanh::lean_dec_ref(v___y_4132_);
                v_size_4136_ = leanh::lean_ctor_get(v___x_4135_, 0);
                leanh::lean_inc(v_size_4136_);
                v_buckets_4137_ = leanh::lean_ctor_get(v___x_4135_, 1);
                leanh::lean_inc_ref(v_buckets_4137_);
                leanh::lean_dec_ref(v___x_4135_);
                v___x_4138_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___closed__2;
                v___x_4139_ = lean_mk_empty_array_with_capacity(v_size_4136_);
                leanh::lean_dec(v_size_4136_);
                v___x_4140_ = lean_array_get_size(v_buckets_4137_);
                v___x_4141_ = lean_nat_dec_lt(v___x_4129_, v___x_4140_);
                if v___x_4141_ == 0 {
                    leanh::lean_dec_ref(v_buckets_4137_);
                    v___y_4121_ = v___x_4138_;
                    v___y_4122_ = v___x_4134_;
                    v___y_4123_ = v___x_4139_;
                    state = 1;
                    continue;
                } else {
                    v___x_4142_ = lean_nat_dec_le(v___x_4140_, v___x_4140_);
                    if v___x_4142_ == 0 {
                        if v___x_4141_ == 0 {
                            leanh::lean_dec_ref(v_buckets_4137_);
                            v___y_4121_ = v___x_4138_;
                            v___y_4122_ = v___x_4134_;
                            v___y_4123_ = v___x_4139_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4143_ = lean_usize_of_nat(v___x_4140_);
                            v___x_4144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_buckets_4137_, v___x_4134_, v___x_4143_, v___x_4139_);
                            leanh::lean_dec_ref(v_buckets_4137_);
                            v___y_4121_ = v___x_4138_;
                            v___y_4122_ = v___x_4134_;
                            v___y_4123_ = v___x_4144_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4145_ = lean_usize_of_nat(v___x_4140_);
                        v___x_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__10(v_buckets_4137_, v___x_4134_, v___x_4145_, v___x_4139_);
                        leanh::lean_dec_ref(v_buckets_4137_);
                        v___y_4121_ = v___x_4138_;
                        v___y_4122_ = v___x_4134_;
                        v___y_4123_ = v___x_4146_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample___boxed(
    mut v_var2Cnf_4157_: *mut leanh::LeanObject,
    mut v_assignment_4158_: *mut leanh::LeanObject,
    mut v_aigSize_4159_: *mut leanh::LeanObject,
    mut v_atomsAssignment_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4161_ = l_Lean_Meta_Tactic_BVDecide_reconstructCounterExample(
        v_var2Cnf_4157_,
        v_assignment_4158_,
        v_aigSize_4159_,
        v_atomsAssignment_4160_,
    );
    leanh::lean_dec_ref(v_atomsAssignment_4160_);
    leanh::lean_dec(v_aigSize_4159_);
    leanh::lean_dec_ref(v_assignment_4158_);
    return v_res_4161_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(
    mut v_as_4162_: *mut leanh::LeanObject,
    mut v_as_x27_4163_: *mut leanh::LeanObject,
    mut v_b_4164_: *mut leanh::LeanObject,
    mut v_a_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg(v_as_x27_4163_, v_b_4164_);
    return v___x_4166_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___boxed(
    mut v_as_4167_: *mut leanh::LeanObject,
    mut v_as_x27_4168_: *mut leanh::LeanObject,
    mut v_b_4169_: *mut leanh::LeanObject,
    mut v_a_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ =
        l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3(
            v_as_4167_,
            v_as_x27_4168_,
            v_b_4169_,
            v_a_4170_,
        );
    leanh::lean_dec(v_as_x27_4168_);
    leanh::lean_dec(v_as_4167_);
    return v_res_4171_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(
    mut v_00_u03b2_4172_: *mut leanh::LeanObject,
    mut v_m_4173_: *mut leanh::LeanObject,
    mut v_a_4174_: *mut leanh::LeanObject,
    mut v_fallback_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___redArg(v_m_4173_, v_a_4174_, v_fallback_4175_);
    return v___x_4176_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4___boxed(
    mut v_00_u03b2_4177_: *mut leanh::LeanObject,
    mut v_m_4178_: *mut leanh::LeanObject,
    mut v_a_4179_: *mut leanh::LeanObject,
    mut v_fallback_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4(v_00_u03b2_4177_, v_m_4178_, v_a_4179_, v_fallback_4180_);
    leanh::lean_dec(v_fallback_4180_);
    leanh::lean_dec(v_a_4179_);
    leanh::lean_dec_ref(v_m_4178_);
    return v_res_4181_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5(
    mut v_00_u03b2_4182_: *mut leanh::LeanObject,
    mut v_k_4183_: *mut leanh::LeanObject,
    mut v_v_4184_: *mut leanh::LeanObject,
    mut v_t_4185_: *mut leanh::LeanObject,
    mut v_hl_4186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4187_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__5___redArg(v_k_4183_, v_v_4184_, v_t_4185_);
    return v___x_4187_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6(
    mut v_00_u03b2_4188_: *mut leanh::LeanObject,
    mut v_m_4189_: *mut leanh::LeanObject,
    mut v_a_4190_: *mut leanh::LeanObject,
    mut v_b_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6___redArg(v_m_4189_, v_a_4190_, v_b_4191_);
    return v___x_4192_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(
    mut v_00_u03b2_4193_: *mut leanh::LeanObject,
    mut v_a_4194_: *mut leanh::LeanObject,
    mut v_fallback_4195_: *mut leanh::LeanObject,
    mut v_x_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___redArg(v_a_4194_, v_fallback_4195_, v_x_4196_);
    return v___x_4197_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5___boxed(
    mut v_00_u03b2_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_fallback_4200_: *mut leanh::LeanObject,
    mut v_x_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__4_spec__5(v_00_u03b2_4198_, v_a_4199_, v_fallback_4200_, v_x_4201_);
    leanh::lean_dec(v_x_4201_);
    leanh::lean_dec(v_fallback_4200_);
    leanh::lean_dec(v_a_4199_);
    return v_res_4202_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(
    mut v_00_u03b2_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
    mut v_x_4205_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4206_: u8 = 0;
    v___x_4206_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___redArg(v_a_4204_, v_x_4205_);
    return v___x_4206_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8___boxed(
    mut v_00_u03b2_4207_: *mut leanh::LeanObject,
    mut v_a_4208_: *mut leanh::LeanObject,
    mut v_x_4209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4210_: u8 = 0;
    let mut v_r_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4210_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__8(v_00_u03b2_4207_, v_a_4208_, v_x_4209_);
    leanh::lean_dec(v_x_4209_);
    leanh::lean_dec(v_a_4208_);
    v_r_4211_ = leanh::lean_box((v_res_4210_) as usize);
    return v_r_4211_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9(
    mut v_00_u03b2_4212_: *mut leanh::LeanObject,
    mut v_data_4213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9___redArg(v_data_4213_);
    return v___x_4214_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10(
    mut v_00_u03b2_4215_: *mut leanh::LeanObject,
    mut v_a_4216_: *mut leanh::LeanObject,
    mut v_b_4217_: *mut leanh::LeanObject,
    mut v_x_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4219_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__10___redArg(v_a_4216_, v_b_4217_, v_x_4218_);
    return v___x_4219_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11(
    mut v_00_u03b2_4220_: *mut leanh::LeanObject,
    mut v_i_4221_: *mut leanh::LeanObject,
    mut v_source_4222_: *mut leanh::LeanObject,
    mut v_target_4223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4224_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11___redArg(v_i_4221_, v_source_4222_, v_target_4223_);
    return v___x_4224_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19(
    mut v_00_u03b2_4225_: *mut leanh::LeanObject,
    mut v_x_4226_: *mut leanh::LeanObject,
    mut v_x_4227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4228_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__6_spec__9_spec__11_spec__19___redArg(v_x_4226_, v_x_4227_);
    return v___x_4228_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(
    mut v_mvarId_4229_: *mut leanh::LeanObject,
    mut v_x_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v_a_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_4229_,
                    v_x_4230_,
                    v___y_4231_,
                    v___y_4232_,
                    v___y_4233_,
                    v___y_4234_,
                );
                if leanh::lean_obj_tag(v___x_4236_) == 0 {
                    v_a_4237_ = leanh::lean_ctor_get(v___x_4236_, 0);
                    v_isSharedCheck_4244_ = (!leanh::lean_is_exclusive(v___x_4236_)) as u8;
                    if v_isSharedCheck_4244_ == 0 {
                        v___x_4239_ = v___x_4236_;
                        v_isShared_4240_ = v_isSharedCheck_4244_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4237_);
                        leanh::lean_dec(v___x_4236_);
                        v___x_4239_ = leanh::lean_box(0);
                        v_isShared_4240_ = v_isSharedCheck_4244_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4245_ = leanh::lean_ctor_get(v___x_4236_, 0);
                    v_isSharedCheck_4252_ = (!leanh::lean_is_exclusive(v___x_4236_)) as u8;
                    if v_isSharedCheck_4252_ == 0 {
                        v___x_4247_ = v___x_4236_;
                        v_isShared_4248_ = v_isSharedCheck_4252_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4245_);
                        leanh::lean_dec(v___x_4236_);
                        v___x_4247_ = leanh::lean_box(0);
                        v_isShared_4248_ = v_isSharedCheck_4252_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4240_ == 0 {
                    v___x_4242_ = v___x_4239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
                    v___x_4242_ = v_reuseFailAlloc_4243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4242_;
            }
            3 => {
                if v_isShared_4248_ == 0 {
                    v___x_4250_ = v___x_4247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
                    v___x_4250_ = v_reuseFailAlloc_4251_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg___boxed(
    mut v_mvarId_4253_: *mut leanh::LeanObject,
    mut v_x_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_4253_, v_x_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
    leanh::lean_dec(v___y_4258_);
    leanh::lean_dec_ref(v___y_4257_);
    leanh::lean_dec(v___y_4256_);
    leanh::lean_dec_ref(v___y_4255_);
    return v_res_4260_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(
    mut v_00_u03b1_4261_: *mut leanh::LeanObject,
    mut v_mvarId_4262_: *mut leanh::LeanObject,
    mut v_x_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
    mut v___y_4266_: *mut leanh::LeanObject,
    mut v___y_4267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_mvarId_4262_, v_x_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
    return v___x_4269_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___boxed(
    mut v_00_u03b1_4270_: *mut leanh::LeanObject,
    mut v_mvarId_4271_: *mut leanh::LeanObject,
    mut v_x_4272_: *mut leanh::LeanObject,
    mut v___y_4273_: *mut leanh::LeanObject,
    mut v___y_4274_: *mut leanh::LeanObject,
    mut v___y_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4278_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0(v_00_u03b1_4270_, v_mvarId_4271_, v_x_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
    leanh::lean_dec(v___y_4276_);
    leanh::lean_dec_ref(v___y_4275_);
    leanh::lean_dec(v___y_4274_);
    leanh::lean_dec_ref(v___y_4273_);
    return v_res_4278_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(
    mut v___x_4279_: *mut leanh::LeanObject,
    mut v_x_4280_: *mut leanh::LeanObject,
    mut v_counterExample_4281_: *mut leanh::LeanObject,
    mut v___y_4282_: *mut leanh::LeanObject,
    mut v___y_4283_: *mut leanh::LeanObject,
    mut v___y_4284_: *mut leanh::LeanObject,
    mut v___y_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v_unused_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4287_ = lean_st_mk_ref(v___x_4279_);
                leanh::lean_inc(v___x_4287_);
                v___x_4288_ = leanh::lean_apply_7(
                    v_x_4280_,
                    v_counterExample_4281_,
                    v___x_4287_,
                    v___y_4282_,
                    v___y_4283_,
                    v___y_4284_,
                    v___y_4285_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4288_) == 0 {
                    v_isSharedCheck_4296_ = (!leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4296_ == 0 {
                        v_unused_4297_ = leanh::lean_ctor_get(v___x_4288_, 0);
                        leanh::lean_dec(v_unused_4297_);
                        v___x_4290_ = v___x_4288_;
                        v_isShared_4291_ = v_isSharedCheck_4296_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4288_);
                        v___x_4290_ = leanh::lean_box(0);
                        v_isShared_4291_ = v_isSharedCheck_4296_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4287_);
                    v_a_4298_ = leanh::lean_ctor_get(v___x_4288_, 0);
                    v_isSharedCheck_4305_ = (!leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4305_ == 0 {
                        v___x_4300_ = v___x_4288_;
                        v_isShared_4301_ = v_isSharedCheck_4305_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4298_);
                        leanh::lean_dec(v___x_4288_);
                        v___x_4300_ = leanh::lean_box(0);
                        v_isShared_4301_ = v_isSharedCheck_4305_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4292_ = lean_st_ref_get(v___x_4287_);
                leanh::lean_dec(v___x_4287_);
                if v_isShared_4291_ == 0 {
                    leanh::lean_ctor_set(v___x_4290_, 0, v___x_4292_);
                    v___x_4294_ = v___x_4290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4292_);
                    v___x_4294_ = v_reuseFailAlloc_4295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4294_;
            }
            3 => {
                if v_isShared_4301_ == 0 {
                    v___x_4303_ = v___x_4300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
                    v___x_4303_ = v_reuseFailAlloc_4304_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed(
    mut v___x_4306_: *mut leanh::LeanObject,
    mut v_x_4307_: *mut leanh::LeanObject,
    mut v_counterExample_4308_: *mut leanh::LeanObject,
    mut v___y_4309_: *mut leanh::LeanObject,
    mut v___y_4310_: *mut leanh::LeanObject,
    mut v___y_4311_: *mut leanh::LeanObject,
    mut v___y_4312_: *mut leanh::LeanObject,
    mut v___y_4313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0(v___x_4306_, v_x_4307_, v_counterExample_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
    return v_res_4314_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4315_ = leanh::lean_box(0);
    v___x_4316_ = leanh::lean_unsigned_to_nat(16);
    v___x_4317_ = lean_mk_array(v___x_4316_, v___x_4315_);
    return v___x_4317_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__0);
    v___x_4319_ = leanh::lean_unsigned_to_nat(0);
    v___x_4320_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4319_);
    leanh::lean_ctor_set(v___x_4320_, 1, v___x_4318_);
    return v___x_4320_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__2;
    v___x_4324_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__1);
    v___x_4325_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4325_, 0, v___x_4324_);
    leanh::lean_ctor_set(v___x_4325_, 1, v___x_4324_);
    leanh::lean_ctor_set(v___x_4325_, 2, v___x_4323_);
    return v___x_4325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(
    mut v_x_4326_: *mut leanh::LeanObject,
    mut v_counterExample_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
    mut v_a_4329_: *mut leanh::LeanObject,
    mut v_a_4330_: *mut leanh::LeanObject,
    mut v_a_4331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_goal_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_goal_4333_ = leanh::lean_ctor_get(v_counterExample_4327_, 0);
    leanh::lean_inc(v_goal_4333_);
    v___x_4334_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___closed__3);
    v___f_4335_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___f_4335_, 0, v___x_4334_);
    leanh::lean_closure_set(v___f_4335_, 1, v_x_4326_);
    leanh::lean_closure_set(v___f_4335_, 2, v_counterExample_4327_);
    v___x_4336_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run_spec__0___redArg(v_goal_4333_, v___f_4335_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
    return v___x_4336_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run___boxed(
    mut v_x_4337_: *mut leanh::LeanObject,
    mut v_counterExample_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
    mut v_a_4341_: *mut leanh::LeanObject,
    mut v_a_4342_: *mut leanh::LeanObject,
    mut v_a_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4344_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v_x_4337_, v_counterExample_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_);
    leanh::lean_dec(v_a_4342_);
    leanh::lean_dec_ref(v_a_4341_);
    leanh::lean_dec(v_a_4340_);
    leanh::lean_dec_ref(v_a_4339_);
    return v_res_4344_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(
    mut v_a_4345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unusedHypotheses_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unusedHypotheses_4347_ = leanh::lean_ctor_get(v_a_4345_, 1);
    leanh::lean_inc_ref(v_unusedHypotheses_4347_);
    v___x_4348_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4348_, 0, v_unusedHypotheses_4347_);
    return v___x_4348_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg___boxed(
    mut v_a_4349_: *mut leanh::LeanObject,
    mut v_a_4350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4351_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___redArg(v_a_4349_);
    leanh::lean_dec_ref(v_a_4349_);
    return v_res_4351_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(
    mut v_a_4352_: *mut leanh::LeanObject,
    mut v_a_4353_: *mut leanh::LeanObject,
    mut v_a_4354_: *mut leanh::LeanObject,
    mut v_a_4355_: *mut leanh::LeanObject,
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unusedHypotheses_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unusedHypotheses_4359_ = leanh::lean_ctor_get(v_a_4352_, 1);
    leanh::lean_inc_ref(v_unusedHypotheses_4359_);
    v___x_4360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4360_, 0, v_unusedHypotheses_4359_);
    return v___x_4360_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps___boxed(
    mut v_a_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
    mut v_a_4363_: *mut leanh::LeanObject,
    mut v_a_4364_: *mut leanh::LeanObject,
    mut v_a_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4368_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_unusedHyps(v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
    leanh::lean_dec(v_a_4366_);
    leanh::lean_dec_ref(v_a_4365_);
    leanh::lean_dec(v_a_4364_);
    leanh::lean_dec_ref(v_a_4363_);
    leanh::lean_dec(v_a_4362_);
    leanh::lean_dec_ref(v_a_4361_);
    return v_res_4368_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(
    mut v_a_4369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_equations_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_equations_4371_ = leanh::lean_ctor_get(v_a_4369_, 2);
    leanh::lean_inc_ref(v_equations_4371_);
    v___x_4372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4372_, 0, v_equations_4371_);
    return v___x_4372_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg___boxed(
    mut v_a_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___redArg(v_a_4373_);
    leanh::lean_dec_ref(v_a_4373_);
    return v_res_4375_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(
    mut v_a_4376_: *mut leanh::LeanObject,
    mut v_a_4377_: *mut leanh::LeanObject,
    mut v_a_4378_: *mut leanh::LeanObject,
    mut v_a_4379_: *mut leanh::LeanObject,
    mut v_a_4380_: *mut leanh::LeanObject,
    mut v_a_4381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_equations_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_equations_4383_ = leanh::lean_ctor_get(v_a_4376_, 2);
    leanh::lean_inc_ref(v_equations_4383_);
    v___x_4384_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4384_, 0, v_equations_4383_);
    return v___x_4384_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations___boxed(
    mut v_a_4385_: *mut leanh::LeanObject,
    mut v_a_4386_: *mut leanh::LeanObject,
    mut v_a_4387_: *mut leanh::LeanObject,
    mut v_a_4388_: *mut leanh::LeanObject,
    mut v_a_4389_: *mut leanh::LeanObject,
    mut v_a_4390_: *mut leanh::LeanObject,
    mut v_a_4391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_equations(v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
    leanh::lean_dec(v_a_4390_);
    leanh::lean_dec_ref(v_a_4389_);
    leanh::lean_dec(v_a_4388_);
    leanh::lean_dec_ref(v_a_4387_);
    leanh::lean_dec(v_a_4386_);
    leanh::lean_dec_ref(v_a_4385_);
    return v_res_4392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(
    mut v_e_4395_: *mut leanh::LeanObject,
    mut v_a_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4398_ = lean_st_ref_take(v_a_4396_);
                v_uninterpretedSymbols_4399_ = leanh::lean_ctor_get(v___x_4398_, 0);
                v_unusedRelevantHypotheses_4400_ = leanh::lean_ctor_get(v___x_4398_, 1);
                v_derivedEquations_4401_ = leanh::lean_ctor_get(v___x_4398_, 2);
                v_isSharedCheck_4414_ = (!leanh::lean_is_exclusive(v___x_4398_)) as u8;
                if v_isSharedCheck_4414_ == 0 {
                    v___x_4403_ = v___x_4398_;
                    v_isShared_4404_ = v_isSharedCheck_4414_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_derivedEquations_4401_);
                    leanh::lean_inc(v_unusedRelevantHypotheses_4400_);
                    leanh::lean_inc(v_uninterpretedSymbols_4399_);
                    leanh::lean_dec(v___x_4398_);
                    v___x_4403_ = leanh::lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4414_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0;
                v___x_4406_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1;
                v___x_4407_ = leanh::lean_box(0);
                v___x_4408_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_4405_,
                    v___x_4406_,
                    v_uninterpretedSymbols_4399_,
                    v_e_4395_,
                    v___x_4407_,
                );
                if v_isShared_4404_ == 0 {
                    leanh::lean_ctor_set(v___x_4403_, 0, v___x_4408_);
                    v___x_4410_ = v___x_4403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4408_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4413_,
                        1,
                        v_unusedRelevantHypotheses_4400_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4413_,
                        2,
                        v_derivedEquations_4401_,
                    );
                    v___x_4410_ = v_reuseFailAlloc_4413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4411_ = lean_st_ref_set(v_a_4396_, v___x_4410_);
                v___x_4412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4412_, 0, v___x_4407_);
                return v___x_4412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___boxed(
    mut v_e_4415_: *mut leanh::LeanObject,
    mut v_a_4416_: *mut leanh::LeanObject,
    mut v_a_4417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4418_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg(v_e_4415_, v_a_4416_);
    leanh::lean_dec(v_a_4416_);
    return v_res_4418_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(
    mut v_e_4419_: *mut leanh::LeanObject,
    mut v_a_4420_: *mut leanh::LeanObject,
    mut v_a_4421_: *mut leanh::LeanObject,
    mut v_a_4422_: *mut leanh::LeanObject,
    mut v_a_4423_: *mut leanh::LeanObject,
    mut v_a_4424_: *mut leanh::LeanObject,
    mut v_a_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4433_: u8 = 0;
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4427_ = lean_st_ref_take(v_a_4421_);
                v_uninterpretedSymbols_4428_ = leanh::lean_ctor_get(v___x_4427_, 0);
                v_unusedRelevantHypotheses_4429_ = leanh::lean_ctor_get(v___x_4427_, 1);
                v_derivedEquations_4430_ = leanh::lean_ctor_get(v___x_4427_, 2);
                v_isSharedCheck_4443_ = (!leanh::lean_is_exclusive(v___x_4427_)) as u8;
                if v_isSharedCheck_4443_ == 0 {
                    v___x_4432_ = v___x_4427_;
                    v_isShared_4433_ = v_isSharedCheck_4443_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_derivedEquations_4430_);
                    leanh::lean_inc(v_unusedRelevantHypotheses_4429_);
                    leanh::lean_inc(v_uninterpretedSymbols_4428_);
                    leanh::lean_dec(v___x_4427_);
                    v___x_4432_ = leanh::lean_box(0);
                    v_isShared_4433_ = v_isSharedCheck_4443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4434_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__0;
                v___x_4435_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___redArg___closed__1;
                v___x_4436_ = leanh::lean_box(0);
                v___x_4437_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_4434_,
                    v___x_4435_,
                    v_uninterpretedSymbols_4428_,
                    v_e_4419_,
                    v___x_4436_,
                );
                if v_isShared_4433_ == 0 {
                    leanh::lean_ctor_set(v___x_4432_, 0, v___x_4437_);
                    v___x_4439_ = v___x_4432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4437_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4442_,
                        1,
                        v_unusedRelevantHypotheses_4429_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4442_,
                        2,
                        v_derivedEquations_4430_,
                    );
                    v___x_4439_ = v_reuseFailAlloc_4442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4440_ = lean_st_ref_set(v_a_4421_, v___x_4439_);
                v___x_4441_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4441_, 0, v___x_4436_);
                return v___x_4441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol___boxed(
    mut v_e_4444_: *mut leanh::LeanObject,
    mut v_a_4445_: *mut leanh::LeanObject,
    mut v_a_4446_: *mut leanh::LeanObject,
    mut v_a_4447_: *mut leanh::LeanObject,
    mut v_a_4448_: *mut leanh::LeanObject,
    mut v_a_4449_: *mut leanh::LeanObject,
    mut v_a_4450_: *mut leanh::LeanObject,
    mut v_a_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4452_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUninterpretedSymbol(v_e_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_);
    leanh::lean_dec(v_a_4450_);
    leanh::lean_dec_ref(v_a_4449_);
    leanh::lean_dec(v_a_4448_);
    leanh::lean_dec_ref(v_a_4447_);
    leanh::lean_dec(v_a_4446_);
    leanh::lean_dec_ref(v_a_4445_);
    return v_res_4452_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(
    mut v_fvar_4455_: *mut leanh::LeanObject,
    mut v_a_4456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4458_ = lean_st_ref_take(v_a_4456_);
                v_uninterpretedSymbols_4459_ = leanh::lean_ctor_get(v___x_4458_, 0);
                v_unusedRelevantHypotheses_4460_ = leanh::lean_ctor_get(v___x_4458_, 1);
                v_derivedEquations_4461_ = leanh::lean_ctor_get(v___x_4458_, 2);
                v_isSharedCheck_4474_ = (!leanh::lean_is_exclusive(v___x_4458_)) as u8;
                if v_isSharedCheck_4474_ == 0 {
                    v___x_4463_ = v___x_4458_;
                    v_isShared_4464_ = v_isSharedCheck_4474_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_derivedEquations_4461_);
                    leanh::lean_inc(v_unusedRelevantHypotheses_4460_);
                    leanh::lean_inc(v_uninterpretedSymbols_4459_);
                    leanh::lean_dec(v___x_4458_);
                    v___x_4463_ = leanh::lean_box(0);
                    v_isShared_4464_ = v_isSharedCheck_4474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4465_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0;
                v___x_4466_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1;
                v___x_4467_ = leanh::lean_box(0);
                v___x_4468_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_4465_,
                    v___x_4466_,
                    v_unusedRelevantHypotheses_4460_,
                    v_fvar_4455_,
                    v___x_4467_,
                );
                if v_isShared_4464_ == 0 {
                    leanh::lean_ctor_set(v___x_4463_, 1, v___x_4468_);
                    v___x_4470_ = v___x_4463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4473_,
                        0,
                        v_uninterpretedSymbols_4459_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___x_4468_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4473_,
                        2,
                        v_derivedEquations_4461_,
                    );
                    v___x_4470_ = v_reuseFailAlloc_4473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4471_ = lean_st_ref_set(v_a_4456_, v___x_4470_);
                v___x_4472_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4472_, 0, v___x_4467_);
                return v___x_4472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___boxed(
    mut v_fvar_4475_: *mut leanh::LeanObject,
    mut v_a_4476_: *mut leanh::LeanObject,
    mut v_a_4477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4478_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg(v_fvar_4475_, v_a_4476_);
    leanh::lean_dec(v_a_4476_);
    return v_res_4478_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(
    mut v_fvar_4479_: *mut leanh::LeanObject,
    mut v_a_4480_: *mut leanh::LeanObject,
    mut v_a_4481_: *mut leanh::LeanObject,
    mut v_a_4482_: *mut leanh::LeanObject,
    mut v_a_4483_: *mut leanh::LeanObject,
    mut v_a_4484_: *mut leanh::LeanObject,
    mut v_a_4485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4487_ = lean_st_ref_take(v_a_4481_);
                v_uninterpretedSymbols_4488_ = leanh::lean_ctor_get(v___x_4487_, 0);
                v_unusedRelevantHypotheses_4489_ = leanh::lean_ctor_get(v___x_4487_, 1);
                v_derivedEquations_4490_ = leanh::lean_ctor_get(v___x_4487_, 2);
                v_isSharedCheck_4503_ = (!leanh::lean_is_exclusive(v___x_4487_)) as u8;
                if v_isSharedCheck_4503_ == 0 {
                    v___x_4492_ = v___x_4487_;
                    v_isShared_4493_ = v_isSharedCheck_4503_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_derivedEquations_4490_);
                    leanh::lean_inc(v_unusedRelevantHypotheses_4489_);
                    leanh::lean_inc(v_uninterpretedSymbols_4488_);
                    leanh::lean_dec(v___x_4487_);
                    v___x_4492_ = leanh::lean_box(0);
                    v_isShared_4493_ = v_isSharedCheck_4503_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4494_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__0;
                v___x_4495_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___redArg___closed__1;
                v___x_4496_ = leanh::lean_box(0);
                v___x_4497_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_4494_,
                    v___x_4495_,
                    v_unusedRelevantHypotheses_4489_,
                    v_fvar_4479_,
                    v___x_4496_,
                );
                if v_isShared_4493_ == 0 {
                    leanh::lean_ctor_set(v___x_4492_, 1, v___x_4497_);
                    v___x_4499_ = v___x_4492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4502_,
                        0,
                        v_uninterpretedSymbols_4488_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 1, v___x_4497_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4502_,
                        2,
                        v_derivedEquations_4490_,
                    );
                    v___x_4499_ = v_reuseFailAlloc_4502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4500_ = lean_st_ref_set(v_a_4481_, v___x_4499_);
                v___x_4501_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4501_, 0, v___x_4496_);
                return v___x_4501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis___boxed(
    mut v_fvar_4504_: *mut leanh::LeanObject,
    mut v_a_4505_: *mut leanh::LeanObject,
    mut v_a_4506_: *mut leanh::LeanObject,
    mut v_a_4507_: *mut leanh::LeanObject,
    mut v_a_4508_: *mut leanh::LeanObject,
    mut v_a_4509_: *mut leanh::LeanObject,
    mut v_a_4510_: *mut leanh::LeanObject,
    mut v_a_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4512_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addUnusedRelevantHypothesis(v_fvar_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
    leanh::lean_dec(v_a_4510_);
    leanh::lean_dec_ref(v_a_4509_);
    leanh::lean_dec(v_a_4508_);
    leanh::lean_dec_ref(v_a_4507_);
    leanh::lean_dec(v_a_4506_);
    leanh::lean_dec_ref(v_a_4505_);
    return v_res_4512_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(
    mut v_var_4513_: *mut leanh::LeanObject,
    mut v_value_4514_: *mut leanh::LeanObject,
    mut v_a_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4517_ = lean_st_ref_take(v_a_4515_);
                v_uninterpretedSymbols_4518_ = leanh::lean_ctor_get(v___x_4517_, 0);
                v_unusedRelevantHypotheses_4519_ = leanh::lean_ctor_get(v___x_4517_, 1);
                v_derivedEquations_4520_ = leanh::lean_ctor_get(v___x_4517_, 2);
                v_isSharedCheck_4532_ = (!leanh::lean_is_exclusive(v___x_4517_)) as u8;
                if v_isSharedCheck_4532_ == 0 {
                    v___x_4522_ = v___x_4517_;
                    v_isShared_4523_ = v_isSharedCheck_4532_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_derivedEquations_4520_);
                    leanh::lean_inc(v_unusedRelevantHypotheses_4519_);
                    leanh::lean_inc(v_uninterpretedSymbols_4518_);
                    leanh::lean_dec(v___x_4517_);
                    v___x_4522_ = leanh::lean_box(0);
                    v_isShared_4523_ = v_isSharedCheck_4532_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4524_, 0, v_var_4513_);
                leanh::lean_ctor_set(v___x_4524_, 1, v_value_4514_);
                v___x_4525_ = lean_array_push(v_derivedEquations_4520_, v___x_4524_);
                if v_isShared_4523_ == 0 {
                    leanh::lean_ctor_set(v___x_4522_, 2, v___x_4525_);
                    v___x_4527_ = v___x_4522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4531_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4531_,
                        0,
                        v_uninterpretedSymbols_4518_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4531_,
                        1,
                        v_unusedRelevantHypotheses_4519_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 2, v___x_4525_);
                    v___x_4527_ = v_reuseFailAlloc_4531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4528_ = lean_st_ref_set(v_a_4515_, v___x_4527_);
                v___x_4529_ = leanh::lean_box(0);
                v___x_4530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4530_, 0, v___x_4529_);
                return v___x_4530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg___boxed(
    mut v_var_4533_: *mut leanh::LeanObject,
    mut v_value_4534_: *mut leanh::LeanObject,
    mut v_a_4535_: *mut leanh::LeanObject,
    mut v_a_4536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4537_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___redArg(v_var_4533_, v_value_4534_, v_a_4535_);
    leanh::lean_dec(v_a_4535_);
    return v_res_4537_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(
    mut v_var_4538_: *mut leanh::LeanObject,
    mut v_value_4539_: *mut leanh::LeanObject,
    mut v_a_4540_: *mut leanh::LeanObject,
    mut v_a_4541_: *mut leanh::LeanObject,
    mut v_a_4542_: *mut leanh::LeanObject,
    mut v_a_4543_: *mut leanh::LeanObject,
    mut v_a_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4553_: u8 = 0;
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4547_ = lean_st_ref_take(v_a_4541_);
                v_uninterpretedSymbols_4548_ = leanh::lean_ctor_get(v___x_4547_, 0);
                v_unusedRelevantHypotheses_4549_ = leanh::lean_ctor_get(v___x_4547_, 1);
                v_derivedEquations_4550_ = leanh::lean_ctor_get(v___x_4547_, 2);
                v_isSharedCheck_4562_ = (!leanh::lean_is_exclusive(v___x_4547_)) as u8;
                if v_isSharedCheck_4562_ == 0 {
                    v___x_4552_ = v___x_4547_;
                    v_isShared_4553_ = v_isSharedCheck_4562_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_derivedEquations_4550_);
                    leanh::lean_inc(v_unusedRelevantHypotheses_4549_);
                    leanh::lean_inc(v_uninterpretedSymbols_4548_);
                    leanh::lean_dec(v___x_4547_);
                    v___x_4552_ = leanh::lean_box(0);
                    v_isShared_4553_ = v_isSharedCheck_4562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4554_, 0, v_var_4538_);
                leanh::lean_ctor_set(v___x_4554_, 1, v_value_4539_);
                v___x_4555_ = lean_array_push(v_derivedEquations_4550_, v___x_4554_);
                if v_isShared_4553_ == 0 {
                    leanh::lean_ctor_set(v___x_4552_, 2, v___x_4555_);
                    v___x_4557_ = v___x_4552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4561_,
                        0,
                        v_uninterpretedSymbols_4548_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4561_,
                        1,
                        v_unusedRelevantHypotheses_4549_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 2, v___x_4555_);
                    v___x_4557_ = v_reuseFailAlloc_4561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4558_ = lean_st_ref_set(v_a_4541_, v___x_4557_);
                v___x_4559_ = leanh::lean_box(0);
                v___x_4560_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4560_, 0, v___x_4559_);
                return v___x_4560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation___boxed(
    mut v_var_4563_: *mut leanh::LeanObject,
    mut v_value_4564_: *mut leanh::LeanObject,
    mut v_a_4565_: *mut leanh::LeanObject,
    mut v_a_4566_: *mut leanh::LeanObject,
    mut v_a_4567_: *mut leanh::LeanObject,
    mut v_a_4568_: *mut leanh::LeanObject,
    mut v_a_4569_: *mut leanh::LeanObject,
    mut v_a_4570_: *mut leanh::LeanObject,
    mut v_a_4571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4572_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_addDerivedEquation(v_var_4563_, v_value_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_);
    leanh::lean_dec(v_a_4570_);
    leanh::lean_dec_ref(v_a_4569_);
    leanh::lean_dec(v_a_4568_);
    leanh::lean_dec_ref(v_a_4567_);
    leanh::lean_dec(v_a_4566_);
    leanh::lean_dec_ref(v_a_4565_);
    return v_res_4572_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(
    mut v_a_4573_: *mut leanh::LeanObject,
    mut v_x_4574_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4575_: u8 = 0;
    let mut v_key_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4574_) == 0 {
                    v___x_4575_ = 0;
                    return v___x_4575_;
                } else {
                    v_key_4576_ = leanh::lean_ctor_get(v_x_4574_, 0);
                    v_tail_4577_ = leanh::lean_ctor_get(v_x_4574_, 2);
                    v___x_4578_ = l_Lean_instBEqFVarId_beq(v_key_4576_, v_a_4573_);
                    if v___x_4578_ == 0 {
                        v_x_4574_ = v_tail_4577_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4578_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg___boxed(
    mut v_a_4580_: *mut leanh::LeanObject,
    mut v_x_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4582_: u8 = 0;
    let mut v_r_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_4580_, v_x_4581_);
    leanh::lean_dec(v_x_4581_);
    leanh::lean_dec(v_a_4580_);
    v_r_4583_ = leanh::lean_box((v_res_4582_) as usize);
    return v_r_4583_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_4584_: *mut leanh::LeanObject,
    mut v_x_4585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: u64 = 0;
    let mut v___x_4594_: u64 = 0;
    let mut v___x_4595_: u64 = 0;
    let mut v_fold_4596_: u64 = 0;
    let mut v___x_4597_: u64 = 0;
    let mut v___x_4598_: u64 = 0;
    let mut v___x_4599_: u64 = 0;
    let mut v___x_4600_: usize = 0;
    let mut v___x_4601_: usize = 0;
    let mut v___x_4602_: usize = 0;
    let mut v___x_4603_: usize = 0;
    let mut v___x_4604_: usize = 0;
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4585_) == 0 {
                    return v_x_4584_;
                } else {
                    v_key_4586_ = leanh::lean_ctor_get(v_x_4585_, 0);
                    v_value_4587_ = leanh::lean_ctor_get(v_x_4585_, 1);
                    v_tail_4588_ = leanh::lean_ctor_get(v_x_4585_, 2);
                    v_isSharedCheck_4611_ = (!leanh::lean_is_exclusive(v_x_4585_)) as u8;
                    if v_isSharedCheck_4611_ == 0 {
                        v___x_4590_ = v_x_4585_;
                        v_isShared_4591_ = v_isSharedCheck_4611_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4588_);
                        leanh::lean_inc(v_value_4587_);
                        leanh::lean_inc(v_key_4586_);
                        leanh::lean_dec(v_x_4585_);
                        v___x_4590_ = leanh::lean_box(0);
                        v_isShared_4591_ = v_isSharedCheck_4611_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4592_ = lean_array_get_size(v_x_4584_);
                v___x_4593_ = l_Lean_instHashableFVarId_hash(v_key_4586_);
                v___x_4594_ = 32u64;
                v___x_4595_ = lean_uint64_shift_right(v___x_4593_, v___x_4594_);
                v_fold_4596_ = lean_uint64_xor(v___x_4593_, v___x_4595_);
                v___x_4597_ = 16u64;
                v___x_4598_ = lean_uint64_shift_right(v_fold_4596_, v___x_4597_);
                v___x_4599_ = lean_uint64_xor(v_fold_4596_, v___x_4598_);
                v___x_4600_ = lean_uint64_to_usize(v___x_4599_);
                v___x_4601_ = lean_usize_of_nat(v___x_4592_);
                v___x_4602_ = 1usize;
                v___x_4603_ = lean_usize_sub(v___x_4601_, v___x_4602_);
                v___x_4604_ = lean_usize_land(v___x_4600_, v___x_4603_);
                v___x_4605_ = lean_array_uget_borrowed(v_x_4584_, v___x_4604_);
                leanh::lean_inc(v___x_4605_);
                if v_isShared_4591_ == 0 {
                    leanh::lean_ctor_set(v___x_4590_, 2, v___x_4605_);
                    v___x_4607_ = v___x_4590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4610_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_key_4586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_value_4587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4610_, 2, v___x_4605_);
                    v___x_4607_ = v_reuseFailAlloc_4610_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4608_ = lean_array_uset(v_x_4584_, v___x_4604_, v___x_4607_);
                v_x_4584_ = v___x_4608_;
                v_x_4585_ = v_tail_4588_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(
    mut v_i_4612_: *mut leanh::LeanObject,
    mut v_source_4613_: *mut leanh::LeanObject,
    mut v_target_4614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v_es_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4615_ = lean_array_get_size(v_source_4613_);
                v___x_4616_ = lean_nat_dec_lt(v_i_4612_, v___x_4615_);
                if v___x_4616_ == 0 {
                    leanh::lean_dec_ref(v_source_4613_);
                    leanh::lean_dec(v_i_4612_);
                    return v_target_4614_;
                } else {
                    v_es_4617_ = lean_array_fget(v_source_4613_, v_i_4612_);
                    v___x_4618_ = leanh::lean_box(0);
                    v_source_4619_ = lean_array_fset(v_source_4613_, v_i_4612_, v___x_4618_);
                    v_target_4620_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_target_4614_, v_es_4617_);
                    v___x_4621_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4622_ = lean_nat_add(v_i_4612_, v___x_4621_);
                    leanh::lean_dec(v_i_4612_);
                    v_i_4612_ = v___x_4622_;
                    v_source_4613_ = v_source_4619_;
                    v_target_4614_ = v_target_4620_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(
    mut v_data_4624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = lean_array_get_size(v_data_4624_);
    v___x_4626_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4627_ = lean_nat_mul(v___x_4625_, v___x_4626_);
    v___x_4628_ = leanh::lean_unsigned_to_nat(0);
    v___x_4629_ = leanh::lean_box(0);
    v___x_4630_ = lean_mk_array(v_nbuckets_4627_, v___x_4629_);
    v___x_4631_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v___x_4628_, v_data_4624_, v___x_4630_);
    return v___x_4631_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(
    mut v_m_4632_: *mut leanh::LeanObject,
    mut v_a_4633_: *mut leanh::LeanObject,
    mut v_b_4634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: u64 = 0;
    let mut v___x_4639_: u64 = 0;
    let mut v___x_4640_: u64 = 0;
    let mut v_fold_4641_: u64 = 0;
    let mut v___x_4642_: u64 = 0;
    let mut v___x_4643_: u64 = 0;
    let mut v___x_4644_: u64 = 0;
    let mut v___x_4645_: usize = 0;
    let mut v___x_4646_: usize = 0;
    let mut v___x_4647_: usize = 0;
    let mut v___x_4648_: usize = 0;
    let mut v___x_4649_: usize = 0;
    let mut v_bkt_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4654_: u8 = 0;
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    let mut v_val_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut v_unused_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4635_ = leanh::lean_ctor_get(v_m_4632_, 0);
                v_buckets_4636_ = leanh::lean_ctor_get(v_m_4632_, 1);
                v___x_4637_ = lean_array_get_size(v_buckets_4636_);
                v___x_4638_ = l_Lean_instHashableFVarId_hash(v_a_4633_);
                v___x_4639_ = 32u64;
                v___x_4640_ = lean_uint64_shift_right(v___x_4638_, v___x_4639_);
                v_fold_4641_ = lean_uint64_xor(v___x_4638_, v___x_4640_);
                v___x_4642_ = 16u64;
                v___x_4643_ = lean_uint64_shift_right(v_fold_4641_, v___x_4642_);
                v___x_4644_ = lean_uint64_xor(v_fold_4641_, v___x_4643_);
                v___x_4645_ = lean_uint64_to_usize(v___x_4644_);
                v___x_4646_ = lean_usize_of_nat(v___x_4637_);
                v___x_4647_ = 1usize;
                v___x_4648_ = lean_usize_sub(v___x_4646_, v___x_4647_);
                v___x_4649_ = lean_usize_land(v___x_4645_, v___x_4648_);
                v_bkt_4650_ = lean_array_uget_borrowed(v_buckets_4636_, v___x_4649_);
                v___x_4651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_4633_, v_bkt_4650_);
                if v___x_4651_ == 0 {
                    leanh::lean_inc_ref(v_buckets_4636_);
                    leanh::lean_inc(v_size_4635_);
                    v_isSharedCheck_4672_ = (!leanh::lean_is_exclusive(v_m_4632_)) as u8;
                    if v_isSharedCheck_4672_ == 0 {
                        v_unused_4673_ = leanh::lean_ctor_get(v_m_4632_, 1);
                        leanh::lean_dec(v_unused_4673_);
                        v_unused_4674_ = leanh::lean_ctor_get(v_m_4632_, 0);
                        leanh::lean_dec(v_unused_4674_);
                        v___x_4653_ = v_m_4632_;
                        v_isShared_4654_ = v_isSharedCheck_4672_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_4632_);
                        v___x_4653_ = leanh::lean_box(0);
                        v_isShared_4654_ = v_isSharedCheck_4672_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_4634_);
                    leanh::lean_dec(v_a_4633_);
                    return v_m_4632_;
                }
            }
            1 => {
                v___x_4655_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_4656_ = lean_nat_add(v_size_4635_, v___x_4655_);
                leanh::lean_dec(v_size_4635_);
                leanh::lean_inc(v_bkt_4650_);
                v___x_4657_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4657_, 0, v_a_4633_);
                leanh::lean_ctor_set(v___x_4657_, 1, v_b_4634_);
                leanh::lean_ctor_set(v___x_4657_, 2, v_bkt_4650_);
                v_buckets_x27_4658_ = lean_array_uset(v_buckets_4636_, v___x_4649_, v___x_4657_);
                v___x_4659_ = leanh::lean_unsigned_to_nat(4);
                v___x_4660_ = lean_nat_mul(v_size_x27_4656_, v___x_4659_);
                v___x_4661_ = leanh::lean_unsigned_to_nat(3);
                v___x_4662_ = lean_nat_div(v___x_4660_, v___x_4661_);
                leanh::lean_dec(v___x_4660_);
                v___x_4663_ = lean_array_get_size(v_buckets_x27_4658_);
                v___x_4664_ = lean_nat_dec_le(v___x_4662_, v___x_4663_);
                leanh::lean_dec(v___x_4662_);
                if v___x_4664_ == 0 {
                    v_val_4665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_buckets_x27_4658_);
                    if v_isShared_4654_ == 0 {
                        leanh::lean_ctor_set(v___x_4653_, 1, v_val_4665_);
                        leanh::lean_ctor_set(v___x_4653_, 0, v_size_x27_4656_);
                        v___x_4667_ = v___x_4653_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_size_x27_4656_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4668_, 1, v_val_4665_);
                        v___x_4667_ = v_reuseFailAlloc_4668_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4654_ == 0 {
                        leanh::lean_ctor_set(v___x_4653_, 1, v_buckets_x27_4658_);
                        leanh::lean_ctor_set(v___x_4653_, 0, v_size_x27_4656_);
                        v___x_4670_ = v___x_4653_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4671_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_size_x27_4656_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 1, v_buckets_x27_4658_);
                        v___x_4670_ = v_reuseFailAlloc_4671_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4667_;
            }
            3 => {
                return v___x_4670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(
    mut v_fvar_4675_: *mut leanh::LeanObject,
    mut v_a_4676_: *mut leanh::LeanObject,
    mut v_a_4677_: *mut leanh::LeanObject,
    mut v___y_4678_: *mut leanh::LeanObject,
    mut v___y_4679_: *mut leanh::LeanObject,
    mut v___y_4680_: *mut leanh::LeanObject,
    mut v___y_4681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut v_a_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4676_) == 0 {
                    v___x_4683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4683_, 0, v_a_4677_);
                    v___x_4684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4684_, 0, v___x_4683_);
                    return v___x_4684_;
                } else {
                    v_key_4685_ = leanh::lean_ctor_get(v_a_4676_, 0);
                    leanh::lean_inc_n(v_key_4685_, 2);
                    v_tail_4686_ = leanh::lean_ctor_get(v_a_4676_, 2);
                    leanh::lean_inc(v_tail_4686_);
                    leanh::lean_dec_ref_known(v_a_4676_, 3);
                    v___x_4687_ = l_Lean_FVarId_getType___redArg(
                        v_key_4685_,
                        v___y_4679_,
                        v___y_4680_,
                        v___y_4681_,
                    );
                    if leanh::lean_obj_tag(v___x_4687_) == 0 {
                        v_a_4688_ = leanh::lean_ctor_get(v___x_4687_, 0);
                        leanh::lean_inc(v_a_4688_);
                        leanh::lean_dec_ref_known(v___x_4687_, 1);
                        v___x_4689_ = leanh::lean_box(0);
                        v___x_4690_ = l_Lean_Expr_containsFVar(v_a_4688_, v_fvar_4675_);
                        leanh::lean_dec(v_a_4688_);
                        if v___x_4690_ == 0 {
                            leanh::lean_dec(v_key_4685_);
                            v_a_4676_ = v_tail_4686_;
                            v_a_4677_ = v___x_4689_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4692_ = lean_st_ref_take(v___y_4678_);
                            v_uninterpretedSymbols_4693_ =
                                leanh::lean_ctor_get(v___x_4692_, 0);
                            v_unusedRelevantHypotheses_4694_ =
                                leanh::lean_ctor_get(v___x_4692_, 1);
                            v_derivedEquations_4695_ = leanh::lean_ctor_get(v___x_4692_, 2);
                            v_isSharedCheck_4705_ =
                                (!leanh::lean_is_exclusive(v___x_4692_)) as u8;
                            if v_isSharedCheck_4705_ == 0 {
                                v___x_4697_ = v___x_4692_;
                                v_isShared_4698_ = v_isSharedCheck_4705_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_derivedEquations_4695_);
                                leanh::lean_inc(v_unusedRelevantHypotheses_4694_);
                                leanh::lean_inc(v_uninterpretedSymbols_4693_);
                                leanh::lean_dec(v___x_4692_);
                                v___x_4697_ = leanh::lean_box(0);
                                v_isShared_4698_ = v_isSharedCheck_4705_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_tail_4686_);
                        leanh::lean_dec(v_key_4685_);
                        v_a_4706_ = leanh::lean_ctor_get(v___x_4687_, 0);
                        v_isSharedCheck_4713_ =
                            (!leanh::lean_is_exclusive(v___x_4687_)) as u8;
                        if v_isSharedCheck_4713_ == 0 {
                            v___x_4708_ = v___x_4687_;
                            v_isShared_4709_ = v_isSharedCheck_4713_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4706_);
                            leanh::lean_dec(v___x_4687_);
                            v___x_4708_ = leanh::lean_box(0);
                            v_isShared_4709_ = v_isSharedCheck_4713_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4699_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_unusedRelevantHypotheses_4694_, v_key_4685_, v___x_4689_);
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 1, v___x_4699_);
                    v___x_4701_ = v___x_4697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4704_,
                        0,
                        v_uninterpretedSymbols_4693_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4699_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4704_,
                        2,
                        v_derivedEquations_4695_,
                    );
                    v___x_4701_ = v_reuseFailAlloc_4704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4702_ = lean_st_ref_set(v___y_4678_, v___x_4701_);
                v_a_4676_ = v_tail_4686_;
                v_a_4677_ = v___x_4689_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4709_ == 0 {
                    v___x_4711_ = v___x_4708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
                    v___x_4711_ = v_reuseFailAlloc_4712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg___boxed(
    mut v_fvar_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
    mut v___y_4718_: *mut leanh::LeanObject,
    mut v___y_4719_: *mut leanh::LeanObject,
    mut v___y_4720_: *mut leanh::LeanObject,
    mut v___y_4721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_4714_, v_a_4715_, v_a_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
    leanh::lean_dec(v___y_4720_);
    leanh::lean_dec_ref(v___y_4719_);
    leanh::lean_dec_ref(v___y_4718_);
    leanh::lean_dec(v___y_4717_);
    leanh::lean_dec(v_fvar_4714_);
    return v_res_4722_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(
    mut v_fvar_4723_: *mut leanh::LeanObject,
    mut v_as_4724_: *mut leanh::LeanObject,
    mut v_sz_4725_: usize,
    mut v_i_4726_: usize,
    mut v_b_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
    mut v___y_4729_: *mut leanh::LeanObject,
    mut v___y_4730_: *mut leanh::LeanObject,
    mut v___y_4731_: *mut leanh::LeanObject,
    mut v___y_4732_: *mut leanh::LeanObject,
    mut v___y_4733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v_a_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: usize = 0;
    let mut v___x_4749_: usize = 0;
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v_a_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4755_: u8 = 0;
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4735_ = lean_usize_dec_lt(v_i_4726_, v_sz_4725_);
                if v___x_4735_ == 0 {
                    v___x_4736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4736_, 0, v_b_4727_);
                    return v___x_4736_;
                } else {
                    v_a_4737_ = lean_array_uget_borrowed(v_as_4724_, v_i_4726_);
                    leanh::lean_inc(v_a_4737_);
                    v___x_4738_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_4723_, v_a_4737_, v_b_4727_, v___y_4729_, v___y_4730_, v___y_4732_, v___y_4733_);
                    if leanh::lean_obj_tag(v___x_4738_) == 0 {
                        v_a_4739_ = leanh::lean_ctor_get(v___x_4738_, 0);
                        v_isSharedCheck_4751_ =
                            (!leanh::lean_is_exclusive(v___x_4738_)) as u8;
                        if v_isSharedCheck_4751_ == 0 {
                            v___x_4741_ = v___x_4738_;
                            v_isShared_4742_ = v_isSharedCheck_4751_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4739_);
                            leanh::lean_dec(v___x_4738_);
                            v___x_4741_ = leanh::lean_box(0);
                            v_isShared_4742_ = v_isSharedCheck_4751_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4752_ = leanh::lean_ctor_get(v___x_4738_, 0);
                        v_isSharedCheck_4759_ =
                            (!leanh::lean_is_exclusive(v___x_4738_)) as u8;
                        if v_isSharedCheck_4759_ == 0 {
                            v___x_4754_ = v___x_4738_;
                            v_isShared_4755_ = v_isSharedCheck_4759_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4752_);
                            leanh::lean_dec(v___x_4738_);
                            v___x_4754_ = leanh::lean_box(0);
                            v_isShared_4755_ = v_isSharedCheck_4759_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4739_) == 0 {
                    v_a_4743_ = leanh::lean_ctor_get(v_a_4739_, 0);
                    leanh::lean_inc(v_a_4743_);
                    leanh::lean_dec_ref_known(v_a_4739_, 1);
                    if v_isShared_4742_ == 0 {
                        leanh::lean_ctor_set(v___x_4741_, 0, v_a_4743_);
                        v___x_4745_ = v___x_4741_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4743_);
                        v___x_4745_ = v_reuseFailAlloc_4746_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4741_);
                    v_a_4747_ = leanh::lean_ctor_get(v_a_4739_, 0);
                    leanh::lean_inc(v_a_4747_);
                    leanh::lean_dec_ref_known(v_a_4739_, 1);
                    v___x_4748_ = 1usize;
                    v___x_4749_ = lean_usize_add(v_i_4726_, v___x_4748_);
                    v_i_4726_ = v___x_4749_;
                    v_b_4727_ = v_a_4747_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4745_;
            }
            3 => {
                if v_isShared_4755_ == 0 {
                    v___x_4757_ = v___x_4754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
                    v___x_4757_ = v_reuseFailAlloc_4758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2___boxed(
    mut v_fvar_4760_: *mut leanh::LeanObject,
    mut v_as_4761_: *mut leanh::LeanObject,
    mut v_sz_4762_: *mut leanh::LeanObject,
    mut v_i_4763_: *mut leanh::LeanObject,
    mut v_b_4764_: *mut leanh::LeanObject,
    mut v___y_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
    mut v___y_4767_: *mut leanh::LeanObject,
    mut v___y_4768_: *mut leanh::LeanObject,
    mut v___y_4769_: *mut leanh::LeanObject,
    mut v___y_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4772_: usize = 0;
    let mut v_i_boxed_4773_: usize = 0;
    let mut v_res_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4772_ = leanh::lean_unbox_usize(v_sz_4762_);
    leanh::lean_dec(v_sz_4762_);
    v_i_boxed_4773_ = leanh::lean_unbox_usize(v_i_4763_);
    leanh::lean_dec(v_i_4763_);
    v_res_4774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_4760_, v_as_4761_, v_sz_boxed_4772_, v_i_boxed_4773_, v_b_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_);
    leanh::lean_dec(v___y_4770_);
    leanh::lean_dec_ref(v___y_4769_);
    leanh::lean_dec(v___y_4768_);
    leanh::lean_dec_ref(v___y_4767_);
    leanh::lean_dec(v___y_4766_);
    leanh::lean_dec_ref(v___y_4765_);
    leanh::lean_dec_ref(v_as_4761_);
    leanh::lean_dec(v_fvar_4760_);
    return v_res_4774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(
    mut v_fvar_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
    mut v_a_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_a_4781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unusedHypotheses_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4786_: usize = 0;
    let mut v___x_4787_: usize = 0;
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4791_: u8 = 0;
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4795_: u8 = 0;
    let mut v_unused_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unusedHypotheses_4783_ = leanh::lean_ctor_get(v_a_4776_, 1);
                v_buckets_4784_ = leanh::lean_ctor_get(v_unusedHypotheses_4783_, 1);
                v___x_4785_ = leanh::lean_box(0);
                v_sz_4786_ = lean_array_size(v_buckets_4784_);
                v___x_4787_ = 0usize;
                v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__2(v_fvar_4775_, v_buckets_4784_, v_sz_4786_, v___x_4787_, v___x_4785_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_);
                if leanh::lean_obj_tag(v___x_4788_) == 0 {
                    v_isSharedCheck_4795_ = (!leanh::lean_is_exclusive(v___x_4788_)) as u8;
                    if v_isSharedCheck_4795_ == 0 {
                        v_unused_4796_ = leanh::lean_ctor_get(v___x_4788_, 0);
                        leanh::lean_dec(v_unused_4796_);
                        v___x_4790_ = v___x_4788_;
                        v_isShared_4791_ = v_isSharedCheck_4795_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4788_);
                        v___x_4790_ = leanh::lean_box(0);
                        v_isShared_4791_ = v_isSharedCheck_4795_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4788_;
                }
            }
            1 => {
                if v_isShared_4791_ == 0 {
                    leanh::lean_ctor_set(v___x_4790_, 0, v___x_4785_);
                    v___x_4793_ = v___x_4790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4785_);
                    v___x_4793_ = v_reuseFailAlloc_4794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed___boxed(
    mut v_fvar_4797_: *mut leanh::LeanObject,
    mut v_a_4798_: *mut leanh::LeanObject,
    mut v_a_4799_: *mut leanh::LeanObject,
    mut v_a_4800_: *mut leanh::LeanObject,
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4805_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvar_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
    leanh::lean_dec(v_a_4803_);
    leanh::lean_dec_ref(v_a_4802_);
    leanh::lean_dec(v_a_4801_);
    leanh::lean_dec_ref(v_a_4800_);
    leanh::lean_dec(v_a_4799_);
    leanh::lean_dec_ref(v_a_4798_);
    leanh::lean_dec(v_fvar_4797_);
    return v_res_4805_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0(
    mut v_00_u03b2_4806_: *mut leanh::LeanObject,
    mut v_m_4807_: *mut leanh::LeanObject,
    mut v_a_4808_: *mut leanh::LeanObject,
    mut v_b_4809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4810_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0___redArg(v_m_4807_, v_a_4808_, v_b_4809_);
    return v___x_4810_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(
    mut v_fvar_4811_: *mut leanh::LeanObject,
    mut v_a_4812_: *mut leanh::LeanObject,
    mut v_a_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
    mut v___y_4816_: *mut leanh::LeanObject,
    mut v___y_4817_: *mut leanh::LeanObject,
    mut v___y_4818_: *mut leanh::LeanObject,
    mut v___y_4819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4821_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___redArg(v_fvar_4811_, v_a_4812_, v_a_4813_, v___y_4815_, v___y_4816_, v___y_4818_, v___y_4819_);
    return v___x_4821_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1___boxed(
    mut v_fvar_4822_: *mut leanh::LeanObject,
    mut v_a_4823_: *mut leanh::LeanObject,
    mut v_a_4824_: *mut leanh::LeanObject,
    mut v___y_4825_: *mut leanh::LeanObject,
    mut v___y_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4832_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__1(v_fvar_4822_, v_a_4823_, v_a_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
    leanh::lean_dec(v___y_4830_);
    leanh::lean_dec_ref(v___y_4829_);
    leanh::lean_dec(v___y_4828_);
    leanh::lean_dec_ref(v___y_4827_);
    leanh::lean_dec(v___y_4826_);
    leanh::lean_dec_ref(v___y_4825_);
    leanh::lean_dec(v_fvar_4822_);
    return v_res_4832_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(
    mut v_00_u03b2_4833_: *mut leanh::LeanObject,
    mut v_a_4834_: *mut leanh::LeanObject,
    mut v_x_4835_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4836_: u8 = 0;
    v___x_4836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___redArg(v_a_4834_, v_x_4835_);
    return v___x_4836_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0___boxed(
    mut v_00_u03b2_4837_: *mut leanh::LeanObject,
    mut v_a_4838_: *mut leanh::LeanObject,
    mut v_x_4839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4840_: u8 = 0;
    let mut v_r_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__0(v_00_u03b2_4837_, v_a_4838_, v_x_4839_);
    leanh::lean_dec(v_x_4839_);
    leanh::lean_dec(v_a_4838_);
    v_r_4841_ = leanh::lean_box((v_res_4840_) as usize);
    return v_r_4841_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1(
    mut v_00_u03b2_4842_: *mut leanh::LeanObject,
    mut v_data_4843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1___redArg(v_data_4843_);
    return v___x_4844_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4845_: *mut leanh::LeanObject,
    mut v_i_4846_: *mut leanh::LeanObject,
    mut v_source_4847_: *mut leanh::LeanObject,
    mut v_target_4848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2___redArg(v_i_4846_, v_source_4847_, v_target_4848_);
    return v___x_4849_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_4850_: *mut leanh::LeanObject,
    mut v_x_4851_: *mut leanh::LeanObject,
    mut v_x_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed_spec__0_spec__1_spec__2_spec__5___redArg(v_x_4851_, v_x_4852_);
    return v___x_4853_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4854_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_4854_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4859_ = l_Lean_instInhabitedExpr;
    v___x_4860_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4860_, 0, v___x_4859_);
    leanh::lean_ctor_set(v___x_4860_, 1, v___x_4859_);
    return v___x_4860_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(
    mut v_msg_4861_: *mut leanh::LeanObject,
    mut v___y_4862_: *mut leanh::LeanObject,
    mut v___y_4863_: *mut leanh::LeanObject,
    mut v___y_4864_: *mut leanh::LeanObject,
    mut v___y_4865_: *mut leanh::LeanObject,
    mut v___y_4866_: *mut leanh::LeanObject,
    mut v___y_4867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v_toFunctor_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___f_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4898_: u8 = 0;
    let mut v_toFunctor_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4905_: u8 = 0;
    let mut v___f_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_23958__overap_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4926_: u8 = 0;
    let mut v_unused_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut v_unused_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4932_: u8 = 0;
    let mut v_unused_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4934_: u8 = 0;
    let mut v_unused_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4869_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__0);
                v___x_4870_ = l_StateRefT_x27_instMonad___redArg(v___x_4869_);
                v_toApplicative_4871_ = leanh::lean_ctor_get(v___x_4870_, 0);
                v_isSharedCheck_4934_ = (!leanh::lean_is_exclusive(v___x_4870_)) as u8;
                if v_isSharedCheck_4934_ == 0 {
                    v_unused_4935_ = leanh::lean_ctor_get(v___x_4870_, 1);
                    leanh::lean_dec(v_unused_4935_);
                    v___x_4873_ = v___x_4870_;
                    v_isShared_4874_ = v_isSharedCheck_4934_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4871_);
                    leanh::lean_dec(v___x_4870_);
                    v___x_4873_ = leanh::lean_box(0);
                    v_isShared_4874_ = v_isSharedCheck_4934_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4875_ = leanh::lean_ctor_get(v_toApplicative_4871_, 0);
                v_toSeq_4876_ = leanh::lean_ctor_get(v_toApplicative_4871_, 2);
                v_toSeqLeft_4877_ = leanh::lean_ctor_get(v_toApplicative_4871_, 3);
                v_toSeqRight_4878_ = leanh::lean_ctor_get(v_toApplicative_4871_, 4);
                v_isSharedCheck_4932_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4871_)) as u8;
                if v_isSharedCheck_4932_ == 0 {
                    v_unused_4933_ = leanh::lean_ctor_get(v_toApplicative_4871_, 1);
                    leanh::lean_dec(v_unused_4933_);
                    v___x_4880_ = v_toApplicative_4871_;
                    v_isShared_4881_ = v_isSharedCheck_4932_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4878_);
                    leanh::lean_inc(v_toSeqLeft_4877_);
                    leanh::lean_inc(v_toSeq_4876_);
                    leanh::lean_inc(v_toFunctor_4875_);
                    leanh::lean_dec(v_toApplicative_4871_);
                    v___x_4880_ = leanh::lean_box(0);
                    v_isShared_4881_ = v_isSharedCheck_4932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4882_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__1;
                v___f_4883_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__2;
                leanh::lean_inc_ref(v_toFunctor_4875_);
                v___f_4884_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4884_, 0, v_toFunctor_4875_);
                v___f_4885_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4885_, 0, v_toFunctor_4875_);
                v___x_4886_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4886_, 0, v___f_4884_);
                leanh::lean_ctor_set(v___x_4886_, 1, v___f_4885_);
                v___f_4887_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4887_, 0, v_toSeqRight_4878_);
                v___f_4888_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4888_, 0, v_toSeqLeft_4877_);
                v___f_4889_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4889_, 0, v_toSeq_4876_);
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v___f_4887_);
                    leanh::lean_ctor_set(v___x_4880_, 3, v___f_4888_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v___f_4889_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v___f_4882_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_4886_);
                    v___x_4891_ = v___x_4880_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4931_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 1, v___f_4882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 2, v___f_4889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 3, v___f_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 4, v___f_4887_);
                    v___x_4891_ = v_reuseFailAlloc_4931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4874_ == 0 {
                    leanh::lean_ctor_set(v___x_4873_, 1, v___f_4883_);
                    leanh::lean_ctor_set(v___x_4873_, 0, v___x_4891_);
                    v___x_4893_ = v___x_4873_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4930_, 1, v___f_4883_);
                    v___x_4893_ = v_reuseFailAlloc_4930_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4894_ = l_StateRefT_x27_instMonad___redArg(v___x_4893_);
                v_toApplicative_4895_ = leanh::lean_ctor_get(v___x_4894_, 0);
                v_isSharedCheck_4928_ = (!leanh::lean_is_exclusive(v___x_4894_)) as u8;
                if v_isSharedCheck_4928_ == 0 {
                    v_unused_4929_ = leanh::lean_ctor_get(v___x_4894_, 1);
                    leanh::lean_dec(v_unused_4929_);
                    v___x_4897_ = v___x_4894_;
                    v_isShared_4898_ = v_isSharedCheck_4928_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4895_);
                    leanh::lean_dec(v___x_4894_);
                    v___x_4897_ = leanh::lean_box(0);
                    v_isShared_4898_ = v_isSharedCheck_4928_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4899_ = leanh::lean_ctor_get(v_toApplicative_4895_, 0);
                v_toSeq_4900_ = leanh::lean_ctor_get(v_toApplicative_4895_, 2);
                v_toSeqLeft_4901_ = leanh::lean_ctor_get(v_toApplicative_4895_, 3);
                v_toSeqRight_4902_ = leanh::lean_ctor_get(v_toApplicative_4895_, 4);
                v_isSharedCheck_4926_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4895_)) as u8;
                if v_isSharedCheck_4926_ == 0 {
                    v_unused_4927_ = leanh::lean_ctor_get(v_toApplicative_4895_, 1);
                    leanh::lean_dec(v_unused_4927_);
                    v___x_4904_ = v_toApplicative_4895_;
                    v_isShared_4905_ = v_isSharedCheck_4926_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4902_);
                    leanh::lean_inc(v_toSeqLeft_4901_);
                    leanh::lean_inc(v_toSeq_4900_);
                    leanh::lean_inc(v_toFunctor_4899_);
                    leanh::lean_dec(v_toApplicative_4895_);
                    v___x_4904_ = leanh::lean_box(0);
                    v_isShared_4905_ = v_isSharedCheck_4926_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4906_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__3;
                v___f_4907_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__4;
                leanh::lean_inc_ref(v_toFunctor_4899_);
                v___f_4908_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4908_, 0, v_toFunctor_4899_);
                v___f_4909_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4909_, 0, v_toFunctor_4899_);
                v___x_4910_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4910_, 0, v___f_4908_);
                leanh::lean_ctor_set(v___x_4910_, 1, v___f_4909_);
                v___f_4911_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4911_, 0, v_toSeqRight_4902_);
                v___f_4912_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4912_, 0, v_toSeqLeft_4901_);
                v___f_4913_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4913_, 0, v_toSeq_4900_);
                if v_isShared_4905_ == 0 {
                    leanh::lean_ctor_set(v___x_4904_, 4, v___f_4911_);
                    leanh::lean_ctor_set(v___x_4904_, 3, v___f_4912_);
                    leanh::lean_ctor_set(v___x_4904_, 2, v___f_4913_);
                    leanh::lean_ctor_set(v___x_4904_, 1, v___f_4906_);
                    leanh::lean_ctor_set(v___x_4904_, 0, v___x_4910_);
                    v___x_4915_ = v___x_4904_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4925_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 1, v___f_4906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 2, v___f_4913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 3, v___f_4912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 4, v___f_4911_);
                    v___x_4915_ = v_reuseFailAlloc_4925_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4898_ == 0 {
                    leanh::lean_ctor_set(v___x_4897_, 1, v___f_4907_);
                    leanh::lean_ctor_set(v___x_4897_, 0, v___x_4915_);
                    v___x_4917_ = v___x_4897_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4924_, 1, v___f_4907_);
                    v___x_4917_ = v_reuseFailAlloc_4924_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4918_ = l_StateRefT_x27_instMonad___redArg(v___x_4917_);
                v___x_4919_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___closed__5);
                v___x_4920_ = l_instInhabitedOfMonad___redArg(v___x_4918_, v___x_4919_);
                v___f_4921_ = leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4921_, 0, v___x_4920_);
                v___x_23958__overap_4922_ = lean_panic_fn_borrowed(v___f_4921_, v_msg_4861_);
                leanh::lean_dec_ref(v___f_4921_);
                leanh::lean_inc(v___y_4867_);
                leanh::lean_inc_ref(v___y_4866_);
                leanh::lean_inc(v___y_4865_);
                leanh::lean_inc_ref(v___y_4864_);
                leanh::lean_inc(v___y_4863_);
                leanh::lean_inc_ref(v___y_4862_);
                v___x_4923_ = leanh::lean_apply_7(
                    v___x_23958__overap_4922_,
                    v___y_4862_,
                    v___y_4863_,
                    v___y_4864_,
                    v___y_4865_,
                    v___y_4866_,
                    v___y_4867_,
                    leanh::lean_box(0),
                );
                return v___x_4923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1___boxed(
    mut v_msg_4936_: *mut leanh::LeanObject,
    mut v___y_4937_: *mut leanh::LeanObject,
    mut v___y_4938_: *mut leanh::LeanObject,
    mut v___y_4939_: *mut leanh::LeanObject,
    mut v___y_4940_: *mut leanh::LeanObject,
    mut v___y_4941_: *mut leanh::LeanObject,
    mut v___y_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4944_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v_msg_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
    leanh::lean_dec(v___y_4942_);
    leanh::lean_dec_ref(v___y_4941_);
    leanh::lean_dec(v___y_4940_);
    leanh::lean_dec_ref(v___y_4939_);
    leanh::lean_dec(v___y_4938_);
    leanh::lean_dec_ref(v___y_4937_);
    return v_res_4944_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(
    mut v_msgData_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
    mut v___y_4947_: *mut leanh::LeanObject,
    mut v___y_4948_: *mut leanh::LeanObject,
    mut v___y_4949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4951_ = lean_st_ref_get(v___y_4949_);
    v_env_4952_ = leanh::lean_ctor_get(v___x_4951_, 0);
    leanh::lean_inc_ref(v_env_4952_);
    leanh::lean_dec(v___x_4951_);
    v___x_4953_ = lean_st_ref_get(v___y_4947_);
    v_mctx_4954_ = leanh::lean_ctor_get(v___x_4953_, 0);
    leanh::lean_inc_ref(v_mctx_4954_);
    leanh::lean_dec(v___x_4953_);
    v_lctx_4955_ = leanh::lean_ctor_get(v___y_4946_, 2);
    v_options_4956_ = leanh::lean_ctor_get(v___y_4948_, 2);
    leanh::lean_inc_ref(v_options_4956_);
    leanh::lean_inc_ref(v_lctx_4955_);
    v___x_4957_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4957_, 0, v_env_4952_);
    leanh::lean_ctor_set(v___x_4957_, 1, v_mctx_4954_);
    leanh::lean_ctor_set(v___x_4957_, 2, v_lctx_4955_);
    leanh::lean_ctor_set(v___x_4957_, 3, v_options_4956_);
    v___x_4958_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4958_, 0, v___x_4957_);
    leanh::lean_ctor_set(v___x_4958_, 1, v_msgData_4945_);
    v___x_4959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4959_, 0, v___x_4958_);
    return v___x_4959_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3___boxed(
    mut v_msgData_4960_: *mut leanh::LeanObject,
    mut v___y_4961_: *mut leanh::LeanObject,
    mut v___y_4962_: *mut leanh::LeanObject,
    mut v___y_4963_: *mut leanh::LeanObject,
    mut v___y_4964_: *mut leanh::LeanObject,
    mut v___y_4965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4966_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msgData_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_);
    leanh::lean_dec(v___y_4964_);
    leanh::lean_dec_ref(v___y_4963_);
    leanh::lean_dec(v___y_4962_);
    leanh::lean_dec_ref(v___y_4961_);
    return v_res_4966_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(
    mut v_msg_4967_: *mut leanh::LeanObject,
    mut v___y_4968_: *mut leanh::LeanObject,
    mut v___y_4969_: *mut leanh::LeanObject,
    mut v___y_4970_: *mut leanh::LeanObject,
    mut v___y_4971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4973_ = leanh::lean_ctor_get(v___y_4970_, 5);
                v___x_4974_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2_spec__3(v_msg_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
                v_a_4975_ = leanh::lean_ctor_get(v___x_4974_, 0);
                v_isSharedCheck_4983_ = (!leanh::lean_is_exclusive(v___x_4974_)) as u8;
                if v_isSharedCheck_4983_ == 0 {
                    v___x_4977_ = v___x_4974_;
                    v_isShared_4978_ = v_isSharedCheck_4983_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4975_);
                    leanh::lean_dec(v___x_4974_);
                    v___x_4977_ = leanh::lean_box(0);
                    v_isShared_4978_ = v_isSharedCheck_4983_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4973_);
                v___x_4979_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4979_, 0, v_ref_4973_);
                leanh::lean_ctor_set(v___x_4979_, 1, v_a_4975_);
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4977_, 1);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_4979_);
                    v___x_4981_ = v___x_4977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4979_);
                    v___x_4981_ = v_reuseFailAlloc_4982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg___boxed(
    mut v_msg_4984_: *mut leanh::LeanObject,
    mut v___y_4985_: *mut leanh::LeanObject,
    mut v___y_4986_: *mut leanh::LeanObject,
    mut v___y_4987_: *mut leanh::LeanObject,
    mut v___y_4988_: *mut leanh::LeanObject,
    mut v___y_4989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4990_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
    leanh::lean_dec(v___y_4988_);
    leanh::lean_dec_ref(v___y_4987_);
    leanh::lean_dec(v___y_4986_);
    leanh::lean_dec_ref(v___y_4985_);
    return v_res_4990_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(
    mut v_ref_4991_: *mut leanh::LeanObject,
    mut v_msg_4992_: *mut leanh::LeanObject,
    mut v___y_4993_: *mut leanh::LeanObject,
    mut v___y_4994_: *mut leanh::LeanObject,
    mut v___y_4995_: *mut leanh::LeanObject,
    mut v___y_4996_: *mut leanh::LeanObject,
    mut v___y_4997_: *mut leanh::LeanObject,
    mut v___y_4998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5012_: u8 = 0;
    let mut v_cancelTk_x3f_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5014_: u8 = 0;
    let mut v_inheritedTraceOptions_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5000_ = leanh::lean_ctor_get(v___y_4997_, 0);
    v_fileMap_5001_ = leanh::lean_ctor_get(v___y_4997_, 1);
    v_options_5002_ = leanh::lean_ctor_get(v___y_4997_, 2);
    v_currRecDepth_5003_ = leanh::lean_ctor_get(v___y_4997_, 3);
    v_maxRecDepth_5004_ = leanh::lean_ctor_get(v___y_4997_, 4);
    v_ref_5005_ = leanh::lean_ctor_get(v___y_4997_, 5);
    v_currNamespace_5006_ = leanh::lean_ctor_get(v___y_4997_, 6);
    v_openDecls_5007_ = leanh::lean_ctor_get(v___y_4997_, 7);
    v_initHeartbeats_5008_ = leanh::lean_ctor_get(v___y_4997_, 8);
    v_maxHeartbeats_5009_ = leanh::lean_ctor_get(v___y_4997_, 9);
    v_quotContext_5010_ = leanh::lean_ctor_get(v___y_4997_, 10);
    v_currMacroScope_5011_ = leanh::lean_ctor_get(v___y_4997_, 11);
    v_diag_5012_ = leanh::lean_ctor_get_uint8(
        v___y_4997_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5013_ = leanh::lean_ctor_get(v___y_4997_, 12);
    v_suppressElabErrors_5014_ = leanh::lean_ctor_get_uint8(
        v___y_4997_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5015_ = leanh::lean_ctor_get(v___y_4997_, 13);
    v_ref_5016_ = l_Lean_replaceRef(v_ref_4991_, v_ref_5005_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5015_);
    leanh::lean_inc(v_cancelTk_x3f_5013_);
    leanh::lean_inc(v_currMacroScope_5011_);
    leanh::lean_inc(v_quotContext_5010_);
    leanh::lean_inc(v_maxHeartbeats_5009_);
    leanh::lean_inc(v_initHeartbeats_5008_);
    leanh::lean_inc(v_openDecls_5007_);
    leanh::lean_inc(v_currNamespace_5006_);
    leanh::lean_inc(v_maxRecDepth_5004_);
    leanh::lean_inc(v_currRecDepth_5003_);
    leanh::lean_inc_ref(v_options_5002_);
    leanh::lean_inc_ref(v_fileMap_5001_);
    leanh::lean_inc_ref(v_fileName_5000_);
    v___x_5017_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5017_, 0, v_fileName_5000_);
    leanh::lean_ctor_set(v___x_5017_, 1, v_fileMap_5001_);
    leanh::lean_ctor_set(v___x_5017_, 2, v_options_5002_);
    leanh::lean_ctor_set(v___x_5017_, 3, v_currRecDepth_5003_);
    leanh::lean_ctor_set(v___x_5017_, 4, v_maxRecDepth_5004_);
    leanh::lean_ctor_set(v___x_5017_, 5, v_ref_5016_);
    leanh::lean_ctor_set(v___x_5017_, 6, v_currNamespace_5006_);
    leanh::lean_ctor_set(v___x_5017_, 7, v_openDecls_5007_);
    leanh::lean_ctor_set(v___x_5017_, 8, v_initHeartbeats_5008_);
    leanh::lean_ctor_set(v___x_5017_, 9, v_maxHeartbeats_5009_);
    leanh::lean_ctor_set(v___x_5017_, 10, v_quotContext_5010_);
    leanh::lean_ctor_set(v___x_5017_, 11, v_currMacroScope_5011_);
    leanh::lean_ctor_set(v___x_5017_, 12, v_cancelTk_x3f_5013_);
    leanh::lean_ctor_set(v___x_5017_, 13, v_inheritedTraceOptions_5015_);
    leanh::lean_ctor_set_uint8(
        v___x_5017_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5012_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5017_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5014_,
    );
    v___x_5018_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_4992_, v___y_4995_, v___y_4996_, v___x_5017_, v___y_4998_);
    leanh::lean_dec_ref_known(v___x_5017_, 14);
    return v___x_5018_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_ref_5019_: *mut leanh::LeanObject,
    mut v_msg_5020_: *mut leanh::LeanObject,
    mut v___y_5021_: *mut leanh::LeanObject,
    mut v___y_5022_: *mut leanh::LeanObject,
    mut v___y_5023_: *mut leanh::LeanObject,
    mut v___y_5024_: *mut leanh::LeanObject,
    mut v___y_5025_: *mut leanh::LeanObject,
    mut v___y_5026_: *mut leanh::LeanObject,
    mut v___y_5027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5028_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_5019_, v_msg_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
    leanh::lean_dec(v___y_5026_);
    leanh::lean_dec_ref(v___y_5025_);
    leanh::lean_dec(v___y_5024_);
    leanh::lean_dec_ref(v___y_5023_);
    leanh::lean_dec(v___y_5022_);
    leanh::lean_dec_ref(v___y_5021_);
    leanh::lean_dec(v_ref_5019_);
    return v_res_5028_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5029_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5029_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5030_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__0);
    v___x_5031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5031_, 0, v___x_5030_);
    return v___x_5031_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5032_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_5033_ = leanh::lean_unsigned_to_nat(0);
    v___x_5034_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_5034_, 0, v___x_5033_);
    leanh::lean_ctor_set(v___x_5034_, 1, v___x_5033_);
    leanh::lean_ctor_set(v___x_5034_, 2, v___x_5033_);
    leanh::lean_ctor_set(v___x_5034_, 3, v___x_5033_);
    leanh::lean_ctor_set(v___x_5034_, 4, v___x_5032_);
    leanh::lean_ctor_set(v___x_5034_, 5, v___x_5032_);
    leanh::lean_ctor_set(v___x_5034_, 6, v___x_5032_);
    leanh::lean_ctor_set(v___x_5034_, 7, v___x_5032_);
    leanh::lean_ctor_set(v___x_5034_, 8, v___x_5032_);
    leanh::lean_ctor_set(v___x_5034_, 9, v___x_5032_);
    return v___x_5034_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5035_ = leanh::lean_unsigned_to_nat(32);
    v___x_5036_ = lean_mk_empty_array_with_capacity(v___x_5035_);
    v___x_5037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5037_, 0, v___x_5036_);
    return v___x_5037_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5038_: usize = 0;
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5038_ = 5usize;
    v___x_5039_ = leanh::lean_unsigned_to_nat(0);
    v___x_5040_ = leanh::lean_unsigned_to_nat(32);
    v___x_5041_ = lean_mk_empty_array_with_capacity(v___x_5040_);
    v___x_5042_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__3);
    v___x_5043_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5043_, 0, v___x_5042_);
    leanh::lean_ctor_set(v___x_5043_, 1, v___x_5041_);
    leanh::lean_ctor_set(v___x_5043_, 2, v___x_5039_);
    leanh::lean_ctor_set(v___x_5043_, 3, v___x_5039_);
    leanh::lean_ctor_set_usize(v___x_5043_, 4, v___x_5038_);
    return v___x_5043_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5044_ = leanh::lean_box(1);
    v___x_5045_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__4);
    v___x_5046_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__1);
    v___x_5047_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5047_, 0, v___x_5046_);
    leanh::lean_ctor_set(v___x_5047_, 1, v___x_5045_);
    leanh::lean_ctor_set(v___x_5047_, 2, v___x_5044_);
    return v___x_5047_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5049_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__6;
    v___x_5050_ = l_Lean_stringToMessageData(v___x_5049_);
    return v___x_5050_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__8;
    v___x_5053_ = l_Lean_stringToMessageData(v___x_5052_);
    return v___x_5053_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5055_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__10;
    v___x_5056_ = l_Lean_stringToMessageData(v___x_5055_);
    return v___x_5056_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5058_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__12;
    v___x_5059_ = l_Lean_stringToMessageData(v___x_5058_);
    return v___x_5059_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5061_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__14;
    v___x_5062_ = l_Lean_stringToMessageData(v___x_5061_);
    return v___x_5062_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5064_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__16;
    v___x_5065_ = l_Lean_stringToMessageData(v___x_5064_);
    return v___x_5065_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5067_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__18;
    v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
    return v___x_5068_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(
    mut v_msg_5069_: *mut leanh::LeanObject,
    mut v_declHint_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: u8 = 0;
    let mut v_isExporting_5076_: u8 = 0;
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5073_ = lean_st_ref_get(v___y_5071_);
                v_env_5074_ = leanh::lean_ctor_get(v___x_5073_, 0);
                leanh::lean_inc_ref(v_env_5074_);
                leanh::lean_dec(v___x_5073_);
                v___x_5075_ = l_Lean_Name_isAnonymous(v_declHint_5070_);
                if v___x_5075_ == 0 {
                    v_isExporting_5076_ = leanh::lean_ctor_get_uint8(
                        v_env_5074_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5076_ == 0 {
                        leanh::lean_dec_ref(v_env_5074_);
                        leanh::lean_dec(v_declHint_5070_);
                        v___x_5077_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5077_, 0, v_msg_5069_);
                        return v___x_5077_;
                    } else {
                        leanh::lean_inc_ref(v_env_5074_);
                        v___x_5078_ = l_Lean_Environment_setExporting(v_env_5074_, v___x_5075_);
                        leanh::lean_inc(v_declHint_5070_);
                        leanh::lean_inc_ref(v___x_5078_);
                        v___x_5079_ = l_Lean_Environment_contains(
                            v___x_5078_,
                            v_declHint_5070_,
                            v_isExporting_5076_,
                        );
                        if v___x_5079_ == 0 {
                            leanh::lean_dec_ref(v___x_5078_);
                            leanh::lean_dec_ref(v_env_5074_);
                            leanh::lean_dec(v_declHint_5070_);
                            v___x_5080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5080_, 0, v_msg_5069_);
                            return v___x_5080_;
                        } else {
                            v___x_5081_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__2);
                            v___x_5082_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__5);
                            v___x_5083_ = l_Lean_Options_empty;
                            v___x_5084_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_5084_, 0, v___x_5078_);
                            leanh::lean_ctor_set(v___x_5084_, 1, v___x_5081_);
                            leanh::lean_ctor_set(v___x_5084_, 2, v___x_5082_);
                            leanh::lean_ctor_set(v___x_5084_, 3, v___x_5083_);
                            leanh::lean_inc(v_declHint_5070_);
                            v___x_5085_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5070_, v___x_5075_);
                            v_c_5086_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_5086_, 0, v___x_5084_);
                            leanh::lean_ctor_set(v_c_5086_, 1, v___x_5085_);
                            v___x_5087_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5074_,
                                v_declHint_5070_,
                            );
                            if leanh::lean_obj_tag(v___x_5087_) == 0 {
                                leanh::lean_dec_ref(v_env_5074_);
                                leanh::lean_dec(v_declHint_5070_);
                                v___x_5088_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
                                v___x_5089_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5089_, 0, v___x_5088_);
                                leanh::lean_ctor_set(v___x_5089_, 1, v_c_5086_);
                                v___x_5090_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__9);
                                v___x_5091_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5091_, 0, v___x_5089_);
                                leanh::lean_ctor_set(v___x_5091_, 1, v___x_5090_);
                                v___x_5092_ = l_Lean_MessageData_note(v___x_5091_);
                                v___x_5093_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_5093_, 0, v_msg_5069_);
                                leanh::lean_ctor_set(v___x_5093_, 1, v___x_5092_);
                                v___x_5094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5094_, 0, v___x_5093_);
                                return v___x_5094_;
                            } else {
                                v_val_5095_ = leanh::lean_ctor_get(v___x_5087_, 0);
                                v_isSharedCheck_5130_ =
                                    (!leanh::lean_is_exclusive(v___x_5087_)) as u8;
                                if v_isSharedCheck_5130_ == 0 {
                                    v___x_5097_ = v___x_5087_;
                                    v_isShared_5098_ = v_isSharedCheck_5130_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_5095_);
                                    leanh::lean_dec(v___x_5087_);
                                    v___x_5097_ = leanh::lean_box(0);
                                    v_isShared_5098_ = v_isSharedCheck_5130_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_5074_);
                    leanh::lean_dec(v_declHint_5070_);
                    v___x_5131_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5131_, 0, v_msg_5069_);
                    return v___x_5131_;
                }
            }
            1 => {
                v___x_5099_ = leanh::lean_box(0);
                v___x_5100_ = l_Lean_Environment_header(v_env_5074_);
                leanh::lean_dec_ref(v_env_5074_);
                v___x_5101_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5100_);
                v_mod_5102_ = lean_array_get(v___x_5099_, v___x_5101_, v_val_5095_);
                leanh::lean_dec(v_val_5095_);
                leanh::lean_dec_ref(v___x_5101_);
                v___x_5103_ = l_Lean_isPrivateName(v_declHint_5070_);
                leanh::lean_dec(v_declHint_5070_);
                if v___x_5103_ == 0 {
                    v___x_5104_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__11);
                    v___x_5105_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5105_, 0, v___x_5104_);
                    leanh::lean_ctor_set(v___x_5105_, 1, v_c_5086_);
                    v___x_5106_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__13);
                    v___x_5107_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5107_, 0, v___x_5105_);
                    leanh::lean_ctor_set(v___x_5107_, 1, v___x_5106_);
                    v___x_5108_ = l_Lean_MessageData_ofName(v_mod_5102_);
                    v___x_5109_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5109_, 0, v___x_5107_);
                    leanh::lean_ctor_set(v___x_5109_, 1, v___x_5108_);
                    v___x_5110_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__15);
                    v___x_5111_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5111_, 0, v___x_5109_);
                    leanh::lean_ctor_set(v___x_5111_, 1, v___x_5110_);
                    v___x_5112_ = l_Lean_MessageData_note(v___x_5111_);
                    v___x_5113_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5113_, 0, v_msg_5069_);
                    leanh::lean_ctor_set(v___x_5113_, 1, v___x_5112_);
                    if v_isShared_5098_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5097_, 0);
                        leanh::lean_ctor_set(v___x_5097_, 0, v___x_5113_);
                        v___x_5115_ = v___x_5097_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5113_);
                        v___x_5115_ = v_reuseFailAlloc_5116_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__7);
                    v___x_5118_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5118_, 0, v___x_5117_);
                    leanh::lean_ctor_set(v___x_5118_, 1, v_c_5086_);
                    v___x_5119_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__17);
                    v___x_5120_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5120_, 0, v___x_5118_);
                    leanh::lean_ctor_set(v___x_5120_, 1, v___x_5119_);
                    v___x_5121_ = l_Lean_MessageData_ofName(v_mod_5102_);
                    v___x_5122_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5122_, 0, v___x_5120_);
                    leanh::lean_ctor_set(v___x_5122_, 1, v___x_5121_);
                    v___x_5123_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___closed__19);
                    v___x_5124_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5124_, 0, v___x_5122_);
                    leanh::lean_ctor_set(v___x_5124_, 1, v___x_5123_);
                    v___x_5125_ = l_Lean_MessageData_note(v___x_5124_);
                    v___x_5126_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5126_, 0, v_msg_5069_);
                    leanh::lean_ctor_set(v___x_5126_, 1, v___x_5125_);
                    if v_isShared_5098_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5097_, 0);
                        leanh::lean_ctor_set(v___x_5097_, 0, v___x_5126_);
                        v___x_5128_ = v___x_5097_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5129_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
                        v___x_5128_ = v_reuseFailAlloc_5129_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5115_;
            }
            3 => {
                return v___x_5128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg___boxed(
    mut v_msg_5132_: *mut leanh::LeanObject,
    mut v_declHint_5133_: *mut leanh::LeanObject,
    mut v___y_5134_: *mut leanh::LeanObject,
    mut v___y_5135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5136_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_5132_, v_declHint_5133_, v___y_5134_);
    leanh::lean_dec(v___y_5134_);
    return v_res_5136_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_msg_5137_: *mut leanh::LeanObject,
    mut v_declHint_5138_: *mut leanh::LeanObject,
    mut v___y_5139_: *mut leanh::LeanObject,
    mut v___y_5140_: *mut leanh::LeanObject,
    mut v___y_5141_: *mut leanh::LeanObject,
    mut v___y_5142_: *mut leanh::LeanObject,
    mut v___y_5143_: *mut leanh::LeanObject,
    mut v___y_5144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5146_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_5137_, v_declHint_5138_, v___y_5144_);
                v_a_5147_ = leanh::lean_ctor_get(v___x_5146_, 0);
                v_isSharedCheck_5156_ = (!leanh::lean_is_exclusive(v___x_5146_)) as u8;
                if v_isSharedCheck_5156_ == 0 {
                    v___x_5149_ = v___x_5146_;
                    v_isShared_5150_ = v_isSharedCheck_5156_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5147_);
                    leanh::lean_dec(v___x_5146_);
                    v___x_5149_ = leanh::lean_box(0);
                    v_isShared_5150_ = v_isSharedCheck_5156_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5151_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5152_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
                leanh::lean_ctor_set(v___x_5152_, 1, v_a_5147_);
                if v_isShared_5150_ == 0 {
                    leanh::lean_ctor_set(v___x_5149_, 0, v___x_5152_);
                    v___x_5154_ = v___x_5149_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(
    mut v_msg_5157_: *mut leanh::LeanObject,
    mut v_declHint_5158_: *mut leanh::LeanObject,
    mut v___y_5159_: *mut leanh::LeanObject,
    mut v___y_5160_: *mut leanh::LeanObject,
    mut v___y_5161_: *mut leanh::LeanObject,
    mut v___y_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
    mut v___y_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5166_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_5157_, v_declHint_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
    leanh::lean_dec(v___y_5164_);
    leanh::lean_dec_ref(v___y_5163_);
    leanh::lean_dec(v___y_5162_);
    leanh::lean_dec_ref(v___y_5161_);
    leanh::lean_dec(v___y_5160_);
    leanh::lean_dec_ref(v___y_5159_);
    return v_res_5166_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_ref_5167_: *mut leanh::LeanObject,
    mut v_msg_5168_: *mut leanh::LeanObject,
    mut v_declHint_5169_: *mut leanh::LeanObject,
    mut v___y_5170_: *mut leanh::LeanObject,
    mut v___y_5171_: *mut leanh::LeanObject,
    mut v___y_5172_: *mut leanh::LeanObject,
    mut v___y_5173_: *mut leanh::LeanObject,
    mut v___y_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5177_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6(v_msg_5168_, v_declHint_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
    v_a_5178_ = leanh::lean_ctor_get(v___x_5177_, 0);
    leanh::lean_inc(v_a_5178_);
    leanh::lean_dec_ref(v___x_5177_);
    v___x_5179_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_5167_, v_a_5178_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
    return v___x_5179_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_ref_5180_: *mut leanh::LeanObject,
    mut v_msg_5181_: *mut leanh::LeanObject,
    mut v_declHint_5182_: *mut leanh::LeanObject,
    mut v___y_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
    mut v___y_5188_: *mut leanh::LeanObject,
    mut v___y_5189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_5180_, v_msg_5181_, v_declHint_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
    leanh::lean_dec(v___y_5188_);
    leanh::lean_dec_ref(v___y_5187_);
    leanh::lean_dec(v___y_5186_);
    leanh::lean_dec_ref(v___y_5185_);
    leanh::lean_dec(v___y_5184_);
    leanh::lean_dec_ref(v___y_5183_);
    leanh::lean_dec(v_ref_5180_);
    return v_res_5190_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5192_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_5193_ = l_Lean_stringToMessageData(v___x_5192_);
    return v___x_5193_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5195_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_5196_ = l_Lean_stringToMessageData(v___x_5195_);
    return v___x_5196_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(
    mut v_ref_5197_: *mut leanh::LeanObject,
    mut v_constName_5198_: *mut leanh::LeanObject,
    mut v___y_5199_: *mut leanh::LeanObject,
    mut v___y_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
    mut v___y_5202_: *mut leanh::LeanObject,
    mut v___y_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_5207_ = 0;
    leanh::lean_inc(v_constName_5198_);
    v___x_5208_ = l_Lean_MessageData_ofConstName(v_constName_5198_, v___x_5207_);
    v___x_5209_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5209_, 0, v___x_5206_);
    leanh::lean_ctor_set(v___x_5209_, 1, v___x_5208_);
    v___x_5210_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_5211_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5211_, 0, v___x_5209_);
    leanh::lean_ctor_set(v___x_5211_, 1, v___x_5210_);
    v___x_5212_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_5197_, v___x_5211_, v_constName_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
    return v___x_5212_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_5213_: *mut leanh::LeanObject,
    mut v_constName_5214_: *mut leanh::LeanObject,
    mut v___y_5215_: *mut leanh::LeanObject,
    mut v___y_5216_: *mut leanh::LeanObject,
    mut v___y_5217_: *mut leanh::LeanObject,
    mut v___y_5218_: *mut leanh::LeanObject,
    mut v___y_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
    mut v___y_5221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5222_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_5213_, v_constName_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_);
    leanh::lean_dec(v___y_5220_);
    leanh::lean_dec_ref(v___y_5219_);
    leanh::lean_dec(v___y_5218_);
    leanh::lean_dec_ref(v___y_5217_);
    leanh::lean_dec(v___y_5216_);
    leanh::lean_dec_ref(v___y_5215_);
    leanh::lean_dec(v_ref_5213_);
    return v_res_5222_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(
    mut v_constName_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
    mut v___y_5225_: *mut leanh::LeanObject,
    mut v___y_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
    mut v___y_5229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_5231_ = leanh::lean_ctor_get(v___y_5228_, 5);
    v___x_5232_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_5231_, v_constName_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
    return v___x_5232_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg___boxed(
    mut v_constName_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
    mut v___y_5239_: *mut leanh::LeanObject,
    mut v___y_5240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5241_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
    leanh::lean_dec(v___y_5239_);
    leanh::lean_dec_ref(v___y_5238_);
    leanh::lean_dec(v___y_5237_);
    leanh::lean_dec_ref(v___y_5236_);
    leanh::lean_dec(v___y_5235_);
    leanh::lean_dec_ref(v___y_5234_);
    return v_res_5241_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(
    mut v_constName_5242_: *mut leanh::LeanObject,
    mut v___y_5243_: *mut leanh::LeanObject,
    mut v___y_5244_: *mut leanh::LeanObject,
    mut v___y_5245_: *mut leanh::LeanObject,
    mut v___y_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5250_ = lean_st_ref_get(v___y_5248_);
                v_env_5251_ = leanh::lean_ctor_get(v___x_5250_, 0);
                leanh::lean_inc_ref(v_env_5251_);
                leanh::lean_dec(v___x_5250_);
                v___x_5252_ = 0;
                leanh::lean_inc(v_constName_5242_);
                v___x_5253_ =
                    l_Lean_Environment_find_x3f(v_env_5251_, v_constName_5242_, v___x_5252_);
                if leanh::lean_obj_tag(v___x_5253_) == 0 {
                    v___x_5254_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
                    return v___x_5254_;
                } else {
                    leanh::lean_dec(v_constName_5242_);
                    v_val_5255_ = leanh::lean_ctor_get(v___x_5253_, 0);
                    v_isSharedCheck_5262_ = (!leanh::lean_is_exclusive(v___x_5253_)) as u8;
                    if v_isSharedCheck_5262_ == 0 {
                        v___x_5257_ = v___x_5253_;
                        v_isShared_5258_ = v_isSharedCheck_5262_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5255_);
                        leanh::lean_dec(v___x_5253_);
                        v___x_5257_ = leanh::lean_box(0);
                        v_isShared_5258_ = v_isSharedCheck_5262_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5258_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5257_, 0);
                    v___x_5260_ = v___x_5257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_val_5255_);
                    v___x_5260_ = v_reuseFailAlloc_5261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0___boxed(
    mut v_constName_5263_: *mut leanh::LeanObject,
    mut v___y_5264_: *mut leanh::LeanObject,
    mut v___y_5265_: *mut leanh::LeanObject,
    mut v___y_5266_: *mut leanh::LeanObject,
    mut v___y_5267_: *mut leanh::LeanObject,
    mut v___y_5268_: *mut leanh::LeanObject,
    mut v___y_5269_: *mut leanh::LeanObject,
    mut v___y_5270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5271_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_constName_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
    leanh::lean_dec(v___y_5269_);
    leanh::lean_dec_ref(v___y_5268_);
    leanh::lean_dec(v___y_5267_);
    leanh::lean_dec_ref(v___y_5266_);
    leanh::lean_dec(v___y_5265_);
    leanh::lean_dec_ref(v___y_5264_);
    return v_res_5271_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5277_ = leanh::lean_box(0);
    v___x_5278_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__2;
    v___x_5279_ = l_Lean_Expr_const___override(v___x_5278_, v___x_5277_);
    return v___x_5279_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5282_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__5;
    v___x_5283_ = leanh::lean_unsigned_to_nat(61);
    v___x_5284_ = leanh::lean_unsigned_to_nat(201);
    v___x_5285_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__4;
    v___x_5286_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_reconstructCounterExample_spec__3___redArg___closed__0;
    v___x_5287_ = l_mkPanicMessageWithDecl(
        v___x_5286_,
        v___x_5285_,
        v___x_5284_,
        v___x_5283_,
        v___x_5282_,
    );
    return v___x_5287_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5330_ = leanh::lean_box(0);
    v___x_5331_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__28;
    v___x_5332_ = l_Lean_mkConst(v___x_5331_, v___x_5330_);
    return v___x_5332_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5337_ = leanh::lean_box(0);
    v___x_5338_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__31;
    v___x_5339_ = l_Lean_mkConst(v___x_5338_, v___x_5337_);
    return v___x_5339_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5341_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__33;
    v___x_5342_ = l_Lean_stringToMessageData(v___x_5341_);
    return v___x_5342_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5344_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__35;
    v___x_5345_ = l_Lean_stringToMessageData(v___x_5344_);
    return v___x_5345_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5350_ = leanh::lean_unsigned_to_nat(0);
    v___x_5351_ = l_Lean_Level_ofNat(v___x_5350_);
    return v___x_5351_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5352_ = leanh::lean_box(0);
    v___x_5353_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__39);
    v___x_5354_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5354_, 0, v___x_5353_);
    leanh::lean_ctor_set(v___x_5354_, 1, v___x_5352_);
    return v___x_5354_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5355_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
    v___x_5356_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__38;
    v___x_5357_ = l_Lean_Expr_const___override(v___x_5356_, v___x_5355_);
    return v___x_5357_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5360_ = leanh::lean_box(0);
    v___x_5361_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__42;
    v___x_5362_ = l_Lean_mkConst(v___x_5361_, v___x_5360_);
    return v___x_5362_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46()
-> *mut leanh::LeanObject {
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5367_ = leanh::lean_box(0);
    v___x_5368_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__45;
    v___x_5369_ = l_Lean_Expr_const___override(v___x_5368_, v___x_5367_);
    return v___x_5369_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48()
-> *mut leanh::LeanObject {
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5371_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__47;
    v___x_5372_ = l_Lean_stringToMessageData(v___x_5371_);
    return v___x_5372_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5375_ = leanh::lean_box(0);
    v___x_5376_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__49;
    v___x_5377_ = l_Lean_mkConst(v___x_5376_, v___x_5375_);
    return v___x_5377_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52()
-> *mut leanh::LeanObject {
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5381_ = leanh::lean_box(0);
    v___x_5382_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__51;
    v___x_5383_ = l_Lean_Expr_const___override(v___x_5382_, v___x_5381_);
    return v___x_5383_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__53;
    v___x_5386_ = l_Lean_stringToMessageData(v___x_5385_);
    return v___x_5386_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56()
-> *mut leanh::LeanObject {
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5389_ = leanh::lean_box(0);
    v___x_5390_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__55;
    v___x_5391_ = l_Lean_mkConst(v___x_5390_, v___x_5389_);
    return v___x_5391_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58()
-> *mut leanh::LeanObject {
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5395_ = leanh::lean_box(0);
    v___x_5396_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__57;
    v___x_5397_ = l_Lean_Expr_const___override(v___x_5396_, v___x_5395_);
    return v___x_5397_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60()
-> *mut leanh::LeanObject {
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__59;
    v___x_5400_ = l_Lean_stringToMessageData(v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62()
-> *mut leanh::LeanObject {
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5403_ = leanh::lean_box(0);
    v___x_5404_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__61;
    v___x_5405_ = l_Lean_mkConst(v___x_5404_, v___x_5403_);
    return v___x_5405_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64()
-> *mut leanh::LeanObject {
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5409_ = leanh::lean_box(0);
    v___x_5410_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__63;
    v___x_5411_ = l_Lean_Expr_const___override(v___x_5410_, v___x_5409_);
    return v___x_5411_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66()
-> *mut leanh::LeanObject {
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5413_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__65;
    v___x_5414_ = l_Lean_stringToMessageData(v___x_5413_);
    return v___x_5414_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67()
-> u8 {
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: u8 = 0;
    v___x_5415_ = leanh::lean_unsigned_to_nat(0);
    v___x_5416_ = lean_int8_of_nat(v___x_5415_);
    return v___x_5416_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71()
-> *mut leanh::LeanObject {
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__40);
    v___x_5423_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__70;
    v___x_5424_ = l_Lean_Expr_const___override(v___x_5423_, v___x_5422_);
    return v___x_5424_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73()
-> *mut leanh::LeanObject {
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5427_ = leanh::lean_box(0);
    v___x_5428_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__72;
    v___x_5429_ = l_Lean_Expr_const___override(v___x_5428_, v___x_5427_);
    return v___x_5429_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76()
-> *mut leanh::LeanObject {
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5434_ = leanh::lean_box(0);
    v___x_5435_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__75;
    v___x_5436_ = l_Lean_Expr_const___override(v___x_5435_, v___x_5434_);
    return v___x_5436_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78()
-> *mut leanh::LeanObject {
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__77;
    v___x_5439_ = l_Lean_stringToMessageData(v___x_5438_);
    return v___x_5439_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79()
-> u16 {
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: u16 = 0;
    v___x_5440_ = leanh::lean_unsigned_to_nat(0);
    v___x_5441_ = lean_int16_of_nat(v___x_5440_);
    return v___x_5441_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81()
-> *mut leanh::LeanObject {
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = leanh::lean_box(0);
    v___x_5445_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__80;
    v___x_5446_ = l_Lean_Expr_const___override(v___x_5445_, v___x_5444_);
    return v___x_5446_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83()
-> *mut leanh::LeanObject {
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5450_ = leanh::lean_box(0);
    v___x_5451_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__82;
    v___x_5452_ = l_Lean_Expr_const___override(v___x_5451_, v___x_5450_);
    return v___x_5452_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85()
-> *mut leanh::LeanObject {
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5454_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__84;
    v___x_5455_ = l_Lean_stringToMessageData(v___x_5454_);
    return v___x_5455_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86()
-> u32 {
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: u32 = 0;
    v___x_5456_ = leanh::lean_unsigned_to_nat(0);
    v___x_5457_ = lean_int32_of_nat(v___x_5456_);
    return v___x_5457_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88()
-> *mut leanh::LeanObject {
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5460_ = leanh::lean_box(0);
    v___x_5461_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__87;
    v___x_5462_ = l_Lean_Expr_const___override(v___x_5461_, v___x_5460_);
    return v___x_5462_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90()
-> *mut leanh::LeanObject {
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5466_ = leanh::lean_box(0);
    v___x_5467_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__89;
    v___x_5468_ = l_Lean_Expr_const___override(v___x_5467_, v___x_5466_);
    return v___x_5468_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92()
-> *mut leanh::LeanObject {
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5470_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__91;
    v___x_5471_ = l_Lean_stringToMessageData(v___x_5470_);
    return v___x_5471_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93()
-> u64 {
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: u64 = 0;
    v___x_5472_ = leanh::lean_unsigned_to_nat(0);
    v___x_5473_ = lean_int64_of_nat(v___x_5472_);
    return v___x_5473_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95()
-> *mut leanh::LeanObject {
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5476_ = leanh::lean_box(0);
    v___x_5477_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__94;
    v___x_5478_ = l_Lean_Expr_const___override(v___x_5477_, v___x_5476_);
    return v___x_5478_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97()
-> *mut leanh::LeanObject {
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5482_ = leanh::lean_box(0);
    v___x_5483_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__96;
    v___x_5484_ = l_Lean_Expr_const___override(v___x_5483_, v___x_5482_);
    return v___x_5484_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(
    mut v_var_5485_: *mut leanh::LeanObject,
    mut v_value_5486_: *mut leanh::LeanObject,
    mut v_a_5487_: *mut leanh::LeanObject,
    mut v_a_5488_: *mut leanh::LeanObject,
    mut v_a_5489_: *mut leanh::LeanObject,
    mut v_a_5490_: *mut leanh::LeanObject,
    mut v_a_5491_: *mut leanh::LeanObject,
    mut v_a_5492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_w_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5499_: u8 = 0;
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5508_: u8 = 0;
    let mut v___x_5509_: u8 = 0;
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___y_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: u8 = 0;
    let mut v_w_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5550_: u8 = 0;
    let mut v_val_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5556_: u8 = 0;
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v_unused_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_a_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: u8 = 0;
    let mut v_arg_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: u8 = 0;
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: u8 = 0;
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: u8 = 0;
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: u8 = 0;
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: u8 = 0;
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: u8 = 0;
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: u8 = 0;
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: u8 = 0;
    let mut v_w_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: u8 = 0;
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: u8 = 0;
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_w_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5662_: u8 = 0;
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: u8 = 0;
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: u16 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5687_: u8 = 0;
    let mut v_w_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5692_: u8 = 0;
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: u8 = 0;
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: u32 = 0;
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5717_: u8 = 0;
    let mut v_w_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5722_: u8 = 0;
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: u8 = 0;
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u64 = 0;
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5747_: u8 = 0;
    let mut v_w_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5752_: u8 = 0;
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: u8 = 0;
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: u8 = 0;
    let mut v___x_5766_: u8 = 0;
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5779_: u8 = 0;
    let mut v_w_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5784_: u8 = 0;
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: u8 = 0;
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: u16 = 0;
    let mut v___x_5798_: u16 = 0;
    let mut v___x_5799_: u8 = 0;
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5811_: u8 = 0;
    let mut v_w_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: u8 = 0;
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: u32 = 0;
    let mut v___x_5830_: u32 = 0;
    let mut v___x_5831_: u8 = 0;
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_w_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5848_: u8 = 0;
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: u8 = 0;
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: u64 = 0;
    let mut v___x_5862_: u64 = 0;
    let mut v___x_5863_: u8 = 0;
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5875_: u8 = 0;
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v_a_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5880_: u8 = 0;
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5884_: u8 = 0;
    let mut v_w_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bv_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5889_: u8 = 0;
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5509_ = l_Lean_Expr_isFVar(v_var_5485_);
                if v___x_5509_ == 0 {
                    leanh::lean_inc_ref(v_var_5485_);
                    v___x_5510_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_var_5485_, v_a_5490_);
                    if leanh::lean_obj_tag(v___x_5510_) == 0 {
                        v_a_5511_ = leanh::lean_ctor_get(v___x_5510_, 0);
                        v_isSharedCheck_5876_ =
                            (!leanh::lean_is_exclusive(v___x_5510_)) as u8;
                        if v_isSharedCheck_5876_ == 0 {
                            v___x_5513_ = v___x_5510_;
                            v_isShared_5514_ = v_isSharedCheck_5876_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5511_);
                            leanh::lean_dec(v___x_5510_);
                            v___x_5513_ = leanh::lean_box(0);
                            v_isShared_5514_ = v_isSharedCheck_5876_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_value_5486_);
                        leanh::lean_dec_ref(v_var_5485_);
                        v_a_5877_ = leanh::lean_ctor_get(v___x_5510_, 0);
                        v_isSharedCheck_5884_ =
                            (!leanh::lean_is_exclusive(v___x_5510_)) as u8;
                        if v_isSharedCheck_5884_ == 0 {
                            v___x_5879_ = v___x_5510_;
                            v_isShared_5880_ = v_isSharedCheck_5884_;
                            state = 40;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5877_);
                            leanh::lean_dec(v___x_5510_);
                            v___x_5879_ = leanh::lean_box(0);
                            v_isShared_5880_ = v_isSharedCheck_5884_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    v_w_5885_ = leanh::lean_ctor_get(v_value_5486_, 0);
                    v_bv_5886_ = leanh::lean_ctor_get(v_value_5486_, 1);
                    v_isSharedCheck_5898_ = (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                    if v_isSharedCheck_5898_ == 0 {
                        v___x_5888_ = v_value_5486_;
                        v_isShared_5889_ = v_isSharedCheck_5898_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_bv_5886_);
                        leanh::lean_inc(v_w_5885_);
                        leanh::lean_dec(v_value_5486_);
                        v___x_5888_ = leanh::lean_box(0);
                        v_isShared_5889_ = v_isSharedCheck_5898_;
                        state = 42;
                        continue;
                    }
                }
            }
            1 => {
                v_w_5495_ = leanh::lean_ctor_get(v_value_5486_, 0);
                v_bv_5496_ = leanh::lean_ctor_get(v_value_5486_, 1);
                v_isSharedCheck_5508_ = (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                if v_isSharedCheck_5508_ == 0 {
                    v___x_5498_ = v_value_5486_;
                    v_isShared_5499_ = v_isSharedCheck_5508_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_bv_5496_);
                    leanh::lean_inc(v_w_5495_);
                    leanh::lean_dec(v_value_5486_);
                    v___x_5498_ = leanh::lean_box(0);
                    v_isShared_5499_ = v_isSharedCheck_5508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5500_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
                v___x_5501_ = l_Lean_mkNatLit(v_w_5495_);
                v___x_5502_ = l_Lean_mkNatLit(v_bv_5496_);
                v___x_5503_ = l_Lean_mkAppB(v___x_5500_, v___x_5501_, v___x_5502_);
                if v_isShared_5499_ == 0 {
                    leanh::lean_ctor_set(v___x_5498_, 1, v___x_5503_);
                    leanh::lean_ctor_set(v___x_5498_, 0, v_var_5485_);
                    v___x_5505_ = v___x_5498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_var_5485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5507_, 1, v___x_5503_);
                    v___x_5505_ = v_reuseFailAlloc_5507_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5506_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5506_, 0, v___x_5505_);
                return v___x_5506_;
            }
            4 => {
                v___x_5579_ = l_Lean_Expr_cleanupAnnotations(v_a_5511_);
                v___x_5580_ = l_Lean_Expr_isApp(v___x_5579_);
                if v___x_5580_ == 0 {
                    leanh::lean_dec_ref(v___x_5579_);
                    v___y_5516_ = v_a_5487_;
                    v___y_5517_ = v_a_5488_;
                    v___y_5518_ = v_a_5489_;
                    v___y_5519_ = v_a_5490_;
                    v___y_5520_ = v_a_5491_;
                    v___y_5521_ = v_a_5492_;
                    state = 5;
                    continue;
                } else {
                    v_arg_5581_ = leanh::lean_ctor_get(v___x_5579_, 1);
                    leanh::lean_inc_ref(v_arg_5581_);
                    v___x_5602_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5579_);
                    v___x_5603_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__9;
                    v___x_5604_ = l_Lean_Expr_isConstOf(v___x_5602_, v___x_5603_);
                    if v___x_5604_ == 0 {
                        v___x_5605_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__11;
                        v___x_5606_ = l_Lean_Expr_isConstOf(v___x_5602_, v___x_5605_);
                        if v___x_5606_ == 0 {
                            v___x_5607_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__13;
                            v___x_5608_ = l_Lean_Expr_isConstOf(v___x_5602_, v___x_5607_);
                            if v___x_5608_ == 0 {
                                v___x_5609_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__15;
                                v___x_5610_ = l_Lean_Expr_isConstOf(v___x_5602_, v___x_5609_);
                                if v___x_5610_ == 0 {
                                    v___x_5611_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__17;
                                    v___x_5612_ = l_Lean_Expr_isConstOf(v___x_5602_, v___x_5611_);
                                    if v___x_5612_ == 0 {
                                        v___x_5613_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__19;
                                        v___x_5614_ =
                                            l_Lean_Expr_isConstOf(v___x_5602_, v___x_5613_);
                                        if v___x_5614_ == 0 {
                                            v___x_5615_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__21;
                                            v___x_5616_ =
                                                l_Lean_Expr_isConstOf(v___x_5602_, v___x_5615_);
                                            if v___x_5616_ == 0 {
                                                v___x_5617_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__23;
                                                v___x_5618_ =
                                                    l_Lean_Expr_isConstOf(v___x_5602_, v___x_5617_);
                                                if v___x_5618_ == 0 {
                                                    v___x_5619_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__25;
                                                    v___x_5620_ = l_Lean_Expr_isConstOf(
                                                        v___x_5602_,
                                                        v___x_5619_,
                                                    );
                                                    leanh::lean_dec_ref(v___x_5602_);
                                                    if v___x_5620_ == 0 {
                                                        leanh::lean_dec_ref(v_arg_5581_);
                                                        v___y_5516_ = v_a_5487_;
                                                        v___y_5517_ = v_a_5488_;
                                                        v___y_5518_ = v_a_5489_;
                                                        v___y_5519_ = v_a_5490_;
                                                        v___y_5520_ = v_a_5491_;
                                                        v___y_5521_ = v_a_5492_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        leanh::lean_del_object(v___x_5513_);
                                                        leanh::lean_dec_ref(v_var_5485_);
                                                        v_w_5621_ = leanh::lean_ctor_get(
                                                            v_value_5486_,
                                                            0,
                                                        );
                                                        leanh::lean_inc(v_w_5621_);
                                                        v_bv_5622_ = leanh::lean_ctor_get(
                                                            v_value_5486_,
                                                            1,
                                                        );
                                                        leanh::lean_inc(v_bv_5622_);
                                                        leanh::lean_dec_ref(v_value_5486_);
                                                        v___x_5623_ =
                                                            leanh::lean_unsigned_to_nat(1);
                                                        v___x_5624_ =
                                                            l_BitVec_ofNat(v_w_5621_, v___x_5623_);
                                                        leanh::lean_dec(v_w_5621_);
                                                        v___x_5625_ = lean_nat_dec_eq(
                                                            v_bv_5622_,
                                                            v___x_5624_,
                                                        );
                                                        leanh::lean_dec(v___x_5624_);
                                                        leanh::lean_dec(v_bv_5622_);
                                                        if v___x_5625_ == 0 {
                                                            v___x_5626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__29);
                                                            v___y_5599_ = v___x_5626_;
                                                            state = 19;
                                                            continue;
                                                        } else {
                                                            v___x_5627_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__32);
                                                            v___y_5599_ = v___x_5627_;
                                                            state = 19;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_5602_);
                                                    leanh::lean_del_object(v___x_5513_);
                                                    leanh::lean_dec_ref(v_var_5485_);
                                                    v_w_5628_ = leanh::lean_ctor_get(
                                                        v_value_5486_,
                                                        0,
                                                    );
                                                    v_bv_5629_ = leanh::lean_ctor_get(
                                                        v_value_5486_,
                                                        1,
                                                    );
                                                    v_isSharedCheck_5657_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v_value_5486_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5657_ == 0 {
                                                        v___x_5631_ = v_value_5486_;
                                                        v_isShared_5632_ = v_isSharedCheck_5657_;
                                                        state = 20;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_bv_5629_);
                                                        leanh::lean_inc(v_w_5628_);
                                                        leanh::lean_dec(v_value_5486_);
                                                        v___x_5631_ = leanh::lean_box(0);
                                                        v_isShared_5632_ = v_isSharedCheck_5657_;
                                                        state = 20;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_5602_);
                                                leanh::lean_del_object(v___x_5513_);
                                                leanh::lean_dec_ref(v_var_5485_);
                                                v_w_5658_ =
                                                    leanh::lean_ctor_get(v_value_5486_, 0);
                                                v_bv_5659_ =
                                                    leanh::lean_ctor_get(v_value_5486_, 1);
                                                v_isSharedCheck_5687_ =
                                                    (!leanh::lean_is_exclusive(
                                                        v_value_5486_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_5687_ == 0 {
                                                    v___x_5661_ = v_value_5486_;
                                                    v_isShared_5662_ = v_isSharedCheck_5687_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_bv_5659_);
                                                    leanh::lean_inc(v_w_5658_);
                                                    leanh::lean_dec(v_value_5486_);
                                                    v___x_5661_ = leanh::lean_box(0);
                                                    v_isShared_5662_ = v_isSharedCheck_5687_;
                                                    state = 23;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_5602_);
                                            leanh::lean_del_object(v___x_5513_);
                                            leanh::lean_dec_ref(v_var_5485_);
                                            v_w_5688_ =
                                                leanh::lean_ctor_get(v_value_5486_, 0);
                                            v_bv_5689_ =
                                                leanh::lean_ctor_get(v_value_5486_, 1);
                                            v_isSharedCheck_5717_ =
                                                (!leanh::lean_is_exclusive(v_value_5486_))
                                                    as u8;
                                            if v_isSharedCheck_5717_ == 0 {
                                                v___x_5691_ = v_value_5486_;
                                                v_isShared_5692_ = v_isSharedCheck_5717_;
                                                state = 26;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_bv_5689_);
                                                leanh::lean_inc(v_w_5688_);
                                                leanh::lean_dec(v_value_5486_);
                                                v___x_5691_ = leanh::lean_box(0);
                                                v_isShared_5692_ = v_isSharedCheck_5717_;
                                                state = 26;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_5602_);
                                        leanh::lean_del_object(v___x_5513_);
                                        leanh::lean_dec_ref(v_var_5485_);
                                        v_w_5718_ = leanh::lean_ctor_get(v_value_5486_, 0);
                                        v_bv_5719_ = leanh::lean_ctor_get(v_value_5486_, 1);
                                        v_isSharedCheck_5747_ =
                                            (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                                        if v_isSharedCheck_5747_ == 0 {
                                            v___x_5721_ = v_value_5486_;
                                            v_isShared_5722_ = v_isSharedCheck_5747_;
                                            state = 29;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_bv_5719_);
                                            leanh::lean_inc(v_w_5718_);
                                            leanh::lean_dec(v_value_5486_);
                                            v___x_5721_ = leanh::lean_box(0);
                                            v_isShared_5722_ = v_isSharedCheck_5747_;
                                            state = 29;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_5602_);
                                    leanh::lean_del_object(v___x_5513_);
                                    leanh::lean_dec_ref(v_var_5485_);
                                    v_w_5748_ = leanh::lean_ctor_get(v_value_5486_, 0);
                                    v_bv_5749_ = leanh::lean_ctor_get(v_value_5486_, 1);
                                    v_isSharedCheck_5779_ =
                                        (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                                    if v_isSharedCheck_5779_ == 0 {
                                        v___x_5751_ = v_value_5486_;
                                        v_isShared_5752_ = v_isSharedCheck_5779_;
                                        state = 32;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_bv_5749_);
                                        leanh::lean_inc(v_w_5748_);
                                        leanh::lean_dec(v_value_5486_);
                                        v___x_5751_ = leanh::lean_box(0);
                                        v_isShared_5752_ = v_isSharedCheck_5779_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_5602_);
                                leanh::lean_del_object(v___x_5513_);
                                leanh::lean_dec_ref(v_var_5485_);
                                v_w_5780_ = leanh::lean_ctor_get(v_value_5486_, 0);
                                v_bv_5781_ = leanh::lean_ctor_get(v_value_5486_, 1);
                                v_isSharedCheck_5811_ =
                                    (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                                if v_isSharedCheck_5811_ == 0 {
                                    v___x_5783_ = v_value_5486_;
                                    v_isShared_5784_ = v_isSharedCheck_5811_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_bv_5781_);
                                    leanh::lean_inc(v_w_5780_);
                                    leanh::lean_dec(v_value_5486_);
                                    v___x_5783_ = leanh::lean_box(0);
                                    v_isShared_5784_ = v_isSharedCheck_5811_;
                                    state = 34;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_5602_);
                            leanh::lean_del_object(v___x_5513_);
                            leanh::lean_dec_ref(v_var_5485_);
                            v_w_5812_ = leanh::lean_ctor_get(v_value_5486_, 0);
                            v_bv_5813_ = leanh::lean_ctor_get(v_value_5486_, 1);
                            v_isSharedCheck_5843_ =
                                (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                            if v_isSharedCheck_5843_ == 0 {
                                v___x_5815_ = v_value_5486_;
                                v_isShared_5816_ = v_isSharedCheck_5843_;
                                state = 36;
                                continue;
                            } else {
                                leanh::lean_inc(v_bv_5813_);
                                leanh::lean_inc(v_w_5812_);
                                leanh::lean_dec(v_value_5486_);
                                v___x_5815_ = leanh::lean_box(0);
                                v_isShared_5816_ = v_isSharedCheck_5843_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5602_);
                        leanh::lean_del_object(v___x_5513_);
                        leanh::lean_dec_ref(v_var_5485_);
                        v_w_5844_ = leanh::lean_ctor_get(v_value_5486_, 0);
                        v_bv_5845_ = leanh::lean_ctor_get(v_value_5486_, 1);
                        v_isSharedCheck_5875_ =
                            (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                        if v_isSharedCheck_5875_ == 0 {
                            v___x_5847_ = v_value_5486_;
                            v_isShared_5848_ = v_isSharedCheck_5875_;
                            state = 38;
                            continue;
                        } else {
                            leanh::lean_inc(v_bv_5845_);
                            leanh::lean_inc(v_w_5844_);
                            leanh::lean_dec(v_value_5486_);
                            v___x_5847_ = leanh::lean_box(0);
                            v_isShared_5848_ = v_isSharedCheck_5875_;
                            state = 38;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_var_5485_) == 5 {
                    v_fn_5522_ = leanh::lean_ctor_get(v_var_5485_, 0);
                    if leanh::lean_obj_tag(v_fn_5522_) == 4 {
                        v_declName_5523_ = leanh::lean_ctor_get(v_fn_5522_, 0);
                        if leanh::lean_obj_tag(v_declName_5523_) == 1 {
                            v_arg_5524_ = leanh::lean_ctor_get(v_var_5485_, 1);
                            v_us_5525_ = leanh::lean_ctor_get(v_fn_5522_, 1);
                            v_pre_5526_ = leanh::lean_ctor_get(v_declName_5523_, 0);
                            v_str_5527_ = leanh::lean_ctor_get(v_declName_5523_, 1);
                            v___x_5528_ = l_Lean_Meta_Tactic_BVDecide_Normalize_enumToBitVecSuffix;
                            v___x_5529_ = lean_string_dec_eq(v_str_5527_, v___x_5528_);
                            if v___x_5529_ == 0 {
                                v_w_5530_ = leanh::lean_ctor_get(v_value_5486_, 0);
                                v_bv_5531_ = leanh::lean_ctor_get(v_value_5486_, 1);
                                v_isSharedCheck_5545_ =
                                    (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                                if v_isSharedCheck_5545_ == 0 {
                                    v___x_5533_ = v_value_5486_;
                                    v_isShared_5534_ = v_isSharedCheck_5545_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_bv_5531_);
                                    leanh::lean_inc(v_w_5530_);
                                    leanh::lean_dec(v_value_5486_);
                                    v___x_5533_ = leanh::lean_box(0);
                                    v_isShared_5534_ = v_isSharedCheck_5545_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                leanh::lean_inc(v_pre_5526_);
                                leanh::lean_inc(v_us_5525_);
                                leanh::lean_inc_ref(v_arg_5524_);
                                leanh::lean_dec_ref_known(v_var_5485_, 2);
                                leanh::lean_del_object(v___x_5513_);
                                v___x_5546_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0(v_pre_5526_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                                if leanh::lean_obj_tag(v___x_5546_) == 0 {
                                    v_a_5547_ = leanh::lean_ctor_get(v___x_5546_, 0);
                                    v_isSharedCheck_5570_ =
                                        (!leanh::lean_is_exclusive(v___x_5546_)) as u8;
                                    if v_isSharedCheck_5570_ == 0 {
                                        v___x_5549_ = v___x_5546_;
                                        v_isShared_5550_ = v_isSharedCheck_5570_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5547_);
                                        leanh::lean_dec(v___x_5546_);
                                        v___x_5549_ = leanh::lean_box(0);
                                        v_isShared_5550_ = v_isSharedCheck_5570_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_us_5525_);
                                    leanh::lean_dec_ref(v_arg_5524_);
                                    leanh::lean_dec_ref(v_value_5486_);
                                    v_a_5571_ = leanh::lean_ctor_get(v___x_5546_, 0);
                                    v_isSharedCheck_5578_ =
                                        (!leanh::lean_is_exclusive(v___x_5546_)) as u8;
                                    if v_isSharedCheck_5578_ == 0 {
                                        v___x_5573_ = v___x_5546_;
                                        v_isShared_5574_ = v_isSharedCheck_5578_;
                                        state = 13;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5571_);
                                        leanh::lean_dec(v___x_5546_);
                                        v___x_5573_ = leanh::lean_box(0);
                                        v_isShared_5574_ = v_isSharedCheck_5578_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_5513_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5513_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5513_);
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_5535_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
                v___x_5536_ = l_Lean_mkNatLit(v_w_5530_);
                v___x_5537_ = l_Lean_mkNatLit(v_bv_5531_);
                v___x_5538_ = l_Lean_mkAppB(v___x_5535_, v___x_5536_, v___x_5537_);
                if v_isShared_5534_ == 0 {
                    leanh::lean_ctor_set(v___x_5533_, 1, v___x_5538_);
                    leanh::lean_ctor_set(v___x_5533_, 0, v_var_5485_);
                    v___x_5540_ = v___x_5533_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5544_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_var_5485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5538_);
                    v___x_5540_ = v_reuseFailAlloc_5544_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5514_ == 0 {
                    leanh::lean_ctor_set(v___x_5513_, 0, v___x_5540_);
                    v___x_5542_ = v___x_5513_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5540_);
                    v___x_5542_ = v_reuseFailAlloc_5543_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5542_;
            }
            9 => {
                if leanh::lean_obj_tag(v_a_5547_) == 5 {
                    v_val_5551_ = leanh::lean_ctor_get(v_a_5547_, 0);
                    leanh::lean_inc_ref(v_val_5551_);
                    leanh::lean_dec_ref_known(v_a_5547_, 1);
                    v_ctors_5552_ = leanh::lean_ctor_get(v_val_5551_, 4);
                    leanh::lean_inc(v_ctors_5552_);
                    leanh::lean_dec_ref(v_val_5551_);
                    v_bv_5553_ = leanh::lean_ctor_get(v_value_5486_, 1);
                    v_isSharedCheck_5566_ = (!leanh::lean_is_exclusive(v_value_5486_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v_unused_5567_ = leanh::lean_ctor_get(v_value_5486_, 0);
                        leanh::lean_dec(v_unused_5567_);
                        v___x_5555_ = v_value_5486_;
                        v_isShared_5556_ = v_isSharedCheck_5566_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_bv_5553_);
                        leanh::lean_dec(v_value_5486_);
                        v___x_5555_ = leanh::lean_box(0);
                        v_isShared_5556_ = v_isSharedCheck_5566_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5549_);
                    leanh::lean_dec(v_a_5547_);
                    leanh::lean_dec(v_us_5525_);
                    leanh::lean_dec_ref(v_arg_5524_);
                    leanh::lean_dec_ref(v_value_5486_);
                    v___x_5568_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__6);
                    v___x_5569_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__1(v___x_5568_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                    return v___x_5569_;
                }
            }
            10 => {
                v___x_5557_ = leanh::lean_box(0);
                v___x_5558_ =
                    l_List_get_x21Internal___redArg(v___x_5557_, v_ctors_5552_, v_bv_5553_);
                leanh::lean_dec(v_ctors_5552_);
                v___x_5559_ = l_Lean_mkConst(v___x_5558_, v_us_5525_);
                if v_isShared_5556_ == 0 {
                    leanh::lean_ctor_set(v___x_5555_, 1, v___x_5559_);
                    leanh::lean_ctor_set(v___x_5555_, 0, v_arg_5524_);
                    v___x_5561_ = v___x_5555_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_arg_5524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5559_);
                    v___x_5561_ = v_reuseFailAlloc_5565_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5550_ == 0 {
                    leanh::lean_ctor_set(v___x_5549_, 0, v___x_5561_);
                    v___x_5563_ = v___x_5549_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5561_);
                    v___x_5563_ = v_reuseFailAlloc_5564_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5563_;
            }
            13 => {
                if v_isShared_5574_ == 0 {
                    v___x_5576_ = v___x_5573_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
                    v___x_5576_ = v_reuseFailAlloc_5577_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5576_;
            }
            15 => {
                v___x_5584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5584_, 0, v_arg_5581_);
                leanh::lean_ctor_set(v___x_5584_, 1, v___y_5583_);
                v___x_5585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5585_, 0, v___x_5584_);
                return v___x_5585_;
            }
            16 => {
                v___x_5588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5588_, 0, v_arg_5581_);
                leanh::lean_ctor_set(v___x_5588_, 1, v___y_5587_);
                v___x_5589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5589_, 0, v___x_5588_);
                return v___x_5589_;
            }
            17 => {
                v___x_5592_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5592_, 0, v_arg_5581_);
                leanh::lean_ctor_set(v___x_5592_, 1, v___y_5591_);
                v___x_5593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5593_, 0, v___x_5592_);
                return v___x_5593_;
            }
            18 => {
                v___x_5596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5596_, 0, v_arg_5581_);
                leanh::lean_ctor_set(v___x_5596_, 1, v___y_5595_);
                v___x_5597_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5597_, 0, v___x_5596_);
                return v___x_5597_;
            }
            19 => {
                leanh::lean_inc_ref(v___y_5599_);
                v___x_5600_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5600_, 0, v_arg_5581_);
                leanh::lean_ctor_set(v___x_5600_, 1, v___y_5599_);
                v___x_5601_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5601_, 0, v___x_5600_);
                return v___x_5601_;
            }
            20 => {
                v___x_5633_ = leanh::lean_unsigned_to_nat(8);
                v___x_5634_ = lean_nat_dec_eq(v_w_5628_, v___x_5633_);
                if v___x_5634_ == 0 {
                    leanh::lean_dec(v_bv_5629_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5635_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__34);
                    v___x_5636_ = l_Nat_reprFast(v_w_5628_);
                    v___x_5637_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5637_, 0, v___x_5636_);
                    v___x_5638_ = l_Lean_MessageData_ofFormat(v___x_5637_);
                    if v_isShared_5632_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5631_, 7);
                        leanh::lean_ctor_set(v___x_5631_, 1, v___x_5638_);
                        leanh::lean_ctor_set(v___x_5631_, 0, v___x_5635_);
                        v___x_5640_ = v___x_5631_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_5644_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5635_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 1, v___x_5638_);
                        v___x_5640_ = v_reuseFailAlloc_5644_;
                        state = 21;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_w_5628_);
                    v___x_5645_ = lean_uint8_of_nat_mk(v_bv_5629_);
                    v___x_5646_ = lean_uint8_to_nat(v___x_5645_);
                    v_r_5647_ = l_Lean_mkRawNatLit(v___x_5646_);
                    v___x_5648_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
                    v___x_5649_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__43);
                    v___x_5650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__46);
                    leanh::lean_inc_ref(v_r_5647_);
                    v___x_5651_ = l_Lean_Expr_app___override(v___x_5650_, v_r_5647_);
                    v___x_5652_ = l_Lean_mkApp3(v___x_5648_, v___x_5649_, v_r_5647_, v___x_5651_);
                    if v_isShared_5632_ == 0 {
                        leanh::lean_ctor_set(v___x_5631_, 1, v___x_5652_);
                        leanh::lean_ctor_set(v___x_5631_, 0, v_arg_5581_);
                        v___x_5654_ = v___x_5631_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_5656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_arg_5581_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 1, v___x_5652_);
                        v___x_5654_ = v_reuseFailAlloc_5656_;
                        state = 22;
                        continue;
                    }
                }
            }
            21 => {
                v___x_5641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5642_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5642_, 0, v___x_5640_);
                leanh::lean_ctor_set(v___x_5642_, 1, v___x_5641_);
                v___x_5643_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5642_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5643_;
            }
            22 => {
                v___x_5655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5655_, 0, v___x_5654_);
                return v___x_5655_;
            }
            23 => {
                v___x_5663_ = leanh::lean_unsigned_to_nat(16);
                v___x_5664_ = lean_nat_dec_eq(v_w_5658_, v___x_5663_);
                if v___x_5664_ == 0 {
                    leanh::lean_dec(v_bv_5659_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5665_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__48);
                    v___x_5666_ = l_Nat_reprFast(v_w_5658_);
                    v___x_5667_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5667_, 0, v___x_5666_);
                    v___x_5668_ = l_Lean_MessageData_ofFormat(v___x_5667_);
                    if v_isShared_5662_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5661_, 7);
                        leanh::lean_ctor_set(v___x_5661_, 1, v___x_5668_);
                        leanh::lean_ctor_set(v___x_5661_, 0, v___x_5665_);
                        v___x_5670_ = v___x_5661_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_5674_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v___x_5665_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 1, v___x_5668_);
                        v___x_5670_ = v_reuseFailAlloc_5674_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_w_5658_);
                    v___x_5675_ = lean_uint16_of_nat_mk(v_bv_5659_);
                    v___x_5676_ = lean_uint16_to_nat(v___x_5675_);
                    v_r_5677_ = l_Lean_mkRawNatLit(v___x_5676_);
                    v___x_5678_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
                    v___x_5679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__50);
                    v___x_5680_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__52);
                    leanh::lean_inc_ref(v_r_5677_);
                    v___x_5681_ = l_Lean_Expr_app___override(v___x_5680_, v_r_5677_);
                    v___x_5682_ = l_Lean_mkApp3(v___x_5678_, v___x_5679_, v_r_5677_, v___x_5681_);
                    if v_isShared_5662_ == 0 {
                        leanh::lean_ctor_set(v___x_5661_, 1, v___x_5682_);
                        leanh::lean_ctor_set(v___x_5661_, 0, v_arg_5581_);
                        v___x_5684_ = v___x_5661_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_5686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_arg_5581_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5686_, 1, v___x_5682_);
                        v___x_5684_ = v_reuseFailAlloc_5686_;
                        state = 25;
                        continue;
                    }
                }
            }
            24 => {
                v___x_5671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5672_, 0, v___x_5670_);
                leanh::lean_ctor_set(v___x_5672_, 1, v___x_5671_);
                v___x_5673_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5672_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5673_;
            }
            25 => {
                v___x_5685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5685_, 0, v___x_5684_);
                return v___x_5685_;
            }
            26 => {
                v___x_5693_ = leanh::lean_unsigned_to_nat(32);
                v___x_5694_ = lean_nat_dec_eq(v_w_5688_, v___x_5693_);
                if v___x_5694_ == 0 {
                    leanh::lean_dec(v_bv_5689_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5695_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__54);
                    v___x_5696_ = l_Nat_reprFast(v_w_5688_);
                    v___x_5697_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5697_, 0, v___x_5696_);
                    v___x_5698_ = l_Lean_MessageData_ofFormat(v___x_5697_);
                    if v_isShared_5692_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5691_, 7);
                        leanh::lean_ctor_set(v___x_5691_, 1, v___x_5698_);
                        leanh::lean_ctor_set(v___x_5691_, 0, v___x_5695_);
                        v___x_5700_ = v___x_5691_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_5704_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 0, v___x_5695_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 1, v___x_5698_);
                        v___x_5700_ = v_reuseFailAlloc_5704_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_w_5688_);
                    v___x_5705_ = lean_uint32_of_nat_mk(v_bv_5689_);
                    v___x_5706_ = lean_uint32_to_nat(v___x_5705_);
                    v_r_5707_ = l_Lean_mkRawNatLit(v___x_5706_);
                    v___x_5708_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
                    v___x_5709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__56);
                    v___x_5710_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__58);
                    leanh::lean_inc_ref(v_r_5707_);
                    v___x_5711_ = l_Lean_Expr_app___override(v___x_5710_, v_r_5707_);
                    v___x_5712_ = l_Lean_mkApp3(v___x_5708_, v___x_5709_, v_r_5707_, v___x_5711_);
                    if v_isShared_5692_ == 0 {
                        leanh::lean_ctor_set(v___x_5691_, 1, v___x_5712_);
                        leanh::lean_ctor_set(v___x_5691_, 0, v_arg_5581_);
                        v___x_5714_ = v___x_5691_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_5716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_arg_5581_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 1, v___x_5712_);
                        v___x_5714_ = v_reuseFailAlloc_5716_;
                        state = 28;
                        continue;
                    }
                }
            }
            27 => {
                v___x_5701_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5702_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5702_, 0, v___x_5700_);
                leanh::lean_ctor_set(v___x_5702_, 1, v___x_5701_);
                v___x_5703_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5702_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5703_;
            }
            28 => {
                v___x_5715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5715_, 0, v___x_5714_);
                return v___x_5715_;
            }
            29 => {
                v___x_5723_ = leanh::lean_unsigned_to_nat(64);
                v___x_5724_ = lean_nat_dec_eq(v_w_5718_, v___x_5723_);
                if v___x_5724_ == 0 {
                    leanh::lean_dec(v_bv_5719_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5725_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__60);
                    v___x_5726_ = l_Nat_reprFast(v_w_5718_);
                    v___x_5727_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5727_, 0, v___x_5726_);
                    v___x_5728_ = l_Lean_MessageData_ofFormat(v___x_5727_);
                    if v_isShared_5722_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5721_, 7);
                        leanh::lean_ctor_set(v___x_5721_, 1, v___x_5728_);
                        leanh::lean_ctor_set(v___x_5721_, 0, v___x_5725_);
                        v___x_5730_ = v___x_5721_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_5734_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5734_, 0, v___x_5725_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5734_, 1, v___x_5728_);
                        v___x_5730_ = v_reuseFailAlloc_5734_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_w_5718_);
                    v___x_5735_ = lean_uint64_of_nat_mk(v_bv_5719_);
                    v___x_5736_ = lean_uint64_to_nat(v___x_5735_);
                    v_r_5737_ = l_Lean_mkRawNatLit(v___x_5736_);
                    v___x_5738_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__41);
                    v___x_5739_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__62);
                    v___x_5740_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__64);
                    leanh::lean_inc_ref(v_r_5737_);
                    v___x_5741_ = l_Lean_Expr_app___override(v___x_5740_, v_r_5737_);
                    v___x_5742_ = l_Lean_mkApp3(v___x_5738_, v___x_5739_, v_r_5737_, v___x_5741_);
                    if v_isShared_5722_ == 0 {
                        leanh::lean_ctor_set(v___x_5721_, 1, v___x_5742_);
                        leanh::lean_ctor_set(v___x_5721_, 0, v_arg_5581_);
                        v___x_5744_ = v___x_5721_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_5746_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_arg_5581_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5746_, 1, v___x_5742_);
                        v___x_5744_ = v_reuseFailAlloc_5746_;
                        state = 31;
                        continue;
                    }
                }
            }
            30 => {
                v___x_5731_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5732_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5732_, 0, v___x_5730_);
                leanh::lean_ctor_set(v___x_5732_, 1, v___x_5731_);
                v___x_5733_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5732_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5733_;
            }
            31 => {
                v___x_5745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5745_, 0, v___x_5744_);
                return v___x_5745_;
            }
            32 => {
                v___x_5753_ = leanh::lean_unsigned_to_nat(8);
                v___x_5754_ = lean_nat_dec_eq(v_w_5748_, v___x_5753_);
                if v___x_5754_ == 0 {
                    leanh::lean_dec(v_bv_5749_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5755_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__66);
                    v___x_5756_ = l_Nat_reprFast(v_w_5748_);
                    v___x_5757_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5757_, 0, v___x_5756_);
                    v___x_5758_ = l_Lean_MessageData_ofFormat(v___x_5757_);
                    if v_isShared_5752_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5751_, 7);
                        leanh::lean_ctor_set(v___x_5751_, 1, v___x_5758_);
                        leanh::lean_ctor_set(v___x_5751_, 0, v___x_5755_);
                        v___x_5760_ = v___x_5751_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_5764_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5755_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 1, v___x_5758_);
                        v___x_5760_ = v_reuseFailAlloc_5764_;
                        state = 33;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5751_);
                    leanh::lean_dec(v_w_5748_);
                    v___x_5765_ = lean_uint8_of_nat_mk(v_bv_5749_);
                    v___x_5766_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__67);
                    v___x_5767_ = lean_int8_dec_le(v___x_5766_, v___x_5765_);
                    if v___x_5767_ == 0 {
                        v___x_5768_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71);
                        v___x_5769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__73);
                        v___x_5770_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__76);
                        v___x_5771_ = lean_int8_to_int(v___x_5765_);
                        v___x_5772_ = lean_int_neg(v___x_5771_);
                        v___x_5773_ = l_Int_toNat(v___x_5772_);
                        leanh::lean_dec(v___x_5772_);
                        v___x_5774_ = l_Lean_instToExprInt8_mkNat(v___x_5773_);
                        v___x_5775_ =
                            l_Lean_mkApp3(v___x_5768_, v___x_5769_, v___x_5770_, v___x_5774_);
                        v___y_5595_ = v___x_5775_;
                        state = 18;
                        continue;
                    } else {
                        v___x_5776_ = lean_int8_to_int(v___x_5765_);
                        v___x_5777_ = l_Int_toNat(v___x_5776_);
                        v___x_5778_ = l_Lean_instToExprInt8_mkNat(v___x_5777_);
                        v___y_5595_ = v___x_5778_;
                        state = 18;
                        continue;
                    }
                }
            }
            33 => {
                v___x_5761_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5762_, 0, v___x_5760_);
                leanh::lean_ctor_set(v___x_5762_, 1, v___x_5761_);
                v___x_5763_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5762_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5763_;
            }
            34 => {
                v___x_5785_ = leanh::lean_unsigned_to_nat(16);
                v___x_5786_ = lean_nat_dec_eq(v_w_5780_, v___x_5785_);
                if v___x_5786_ == 0 {
                    leanh::lean_dec(v_bv_5781_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__78);
                    v___x_5788_ = l_Nat_reprFast(v_w_5780_);
                    v___x_5789_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5789_, 0, v___x_5788_);
                    v___x_5790_ = l_Lean_MessageData_ofFormat(v___x_5789_);
                    if v_isShared_5784_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5783_, 7);
                        leanh::lean_ctor_set(v___x_5783_, 1, v___x_5790_);
                        leanh::lean_ctor_set(v___x_5783_, 0, v___x_5787_);
                        v___x_5792_ = v___x_5783_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_5796_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5787_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5796_, 1, v___x_5790_);
                        v___x_5792_ = v_reuseFailAlloc_5796_;
                        state = 35;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5783_);
                    leanh::lean_dec(v_w_5780_);
                    v___x_5797_ = lean_uint16_of_nat_mk(v_bv_5781_);
                    v___x_5798_ = leanh::lean_uint16_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__79);
                    v___x_5799_ = lean_int16_dec_le(v___x_5798_, v___x_5797_);
                    if v___x_5799_ == 0 {
                        v___x_5800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71);
                        v___x_5801_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__81);
                        v___x_5802_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__83);
                        v___x_5803_ = lean_int16_to_int(v___x_5797_);
                        v___x_5804_ = lean_int_neg(v___x_5803_);
                        v___x_5805_ = l_Int_toNat(v___x_5804_);
                        leanh::lean_dec(v___x_5804_);
                        v___x_5806_ = l_Lean_instToExprInt16_mkNat(v___x_5805_);
                        v___x_5807_ =
                            l_Lean_mkApp3(v___x_5800_, v___x_5801_, v___x_5802_, v___x_5806_);
                        v___y_5591_ = v___x_5807_;
                        state = 17;
                        continue;
                    } else {
                        v___x_5808_ = lean_int16_to_int(v___x_5797_);
                        v___x_5809_ = l_Int_toNat(v___x_5808_);
                        v___x_5810_ = l_Lean_instToExprInt16_mkNat(v___x_5809_);
                        v___y_5591_ = v___x_5810_;
                        state = 17;
                        continue;
                    }
                }
            }
            35 => {
                v___x_5793_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5794_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5794_, 0, v___x_5792_);
                leanh::lean_ctor_set(v___x_5794_, 1, v___x_5793_);
                v___x_5795_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5794_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5795_;
            }
            36 => {
                v___x_5817_ = leanh::lean_unsigned_to_nat(32);
                v___x_5818_ = lean_nat_dec_eq(v_w_5812_, v___x_5817_);
                if v___x_5818_ == 0 {
                    leanh::lean_dec(v_bv_5813_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__85);
                    v___x_5820_ = l_Nat_reprFast(v_w_5812_);
                    v___x_5821_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5821_, 0, v___x_5820_);
                    v___x_5822_ = l_Lean_MessageData_ofFormat(v___x_5821_);
                    if v_isShared_5816_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5815_, 7);
                        leanh::lean_ctor_set(v___x_5815_, 1, v___x_5822_);
                        leanh::lean_ctor_set(v___x_5815_, 0, v___x_5819_);
                        v___x_5824_ = v___x_5815_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_5828_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5819_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 1, v___x_5822_);
                        v___x_5824_ = v_reuseFailAlloc_5828_;
                        state = 37;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5815_);
                    leanh::lean_dec(v_w_5812_);
                    v___x_5829_ = lean_uint32_of_nat_mk(v_bv_5813_);
                    v___x_5830_ = leanh::lean_uint32_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__86);
                    v___x_5831_ = lean_int32_dec_le(v___x_5830_, v___x_5829_);
                    if v___x_5831_ == 0 {
                        v___x_5832_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71);
                        v___x_5833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__88);
                        v___x_5834_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__90);
                        v___x_5835_ = lean_int32_to_int(v___x_5829_);
                        v___x_5836_ = lean_int_neg(v___x_5835_);
                        leanh::lean_dec(v___x_5835_);
                        v___x_5837_ = l_Int_toNat(v___x_5836_);
                        leanh::lean_dec(v___x_5836_);
                        v___x_5838_ = l_Lean_instToExprInt32_mkNat(v___x_5837_);
                        v___x_5839_ =
                            l_Lean_mkApp3(v___x_5832_, v___x_5833_, v___x_5834_, v___x_5838_);
                        v___y_5587_ = v___x_5839_;
                        state = 16;
                        continue;
                    } else {
                        v___x_5840_ = lean_int32_to_int(v___x_5829_);
                        v___x_5841_ = l_Int_toNat(v___x_5840_);
                        leanh::lean_dec(v___x_5840_);
                        v___x_5842_ = l_Lean_instToExprInt32_mkNat(v___x_5841_);
                        v___y_5587_ = v___x_5842_;
                        state = 16;
                        continue;
                    }
                }
            }
            37 => {
                v___x_5825_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5826_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5826_, 0, v___x_5824_);
                leanh::lean_ctor_set(v___x_5826_, 1, v___x_5825_);
                v___x_5827_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5826_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5827_;
            }
            38 => {
                v___x_5849_ = leanh::lean_unsigned_to_nat(64);
                v___x_5850_ = lean_nat_dec_eq(v_w_5844_, v___x_5849_);
                if v___x_5850_ == 0 {
                    leanh::lean_dec(v_bv_5845_);
                    leanh::lean_dec_ref(v_arg_5581_);
                    v___x_5851_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__92);
                    v___x_5852_ = l_Nat_reprFast(v_w_5844_);
                    v___x_5853_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5853_, 0, v___x_5852_);
                    v___x_5854_ = l_Lean_MessageData_ofFormat(v___x_5853_);
                    if v_isShared_5848_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5847_, 7);
                        leanh::lean_ctor_set(v___x_5847_, 1, v___x_5854_);
                        leanh::lean_ctor_set(v___x_5847_, 0, v___x_5851_);
                        v___x_5856_ = v___x_5847_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_5860_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5860_, 0, v___x_5851_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5860_, 1, v___x_5854_);
                        v___x_5856_ = v_reuseFailAlloc_5860_;
                        state = 39;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5847_);
                    leanh::lean_dec(v_w_5844_);
                    v___x_5861_ = lean_uint64_of_nat_mk(v_bv_5845_);
                    v___x_5862_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__93);
                    v___x_5863_ = lean_int64_dec_le(v___x_5862_, v___x_5861_);
                    if v___x_5863_ == 0 {
                        v___x_5864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__71);
                        v___x_5865_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__95);
                        v___x_5866_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__97);
                        v___x_5867_ = lean_int64_to_int_sint(v___x_5861_);
                        v___x_5868_ = lean_int_neg(v___x_5867_);
                        leanh::lean_dec(v___x_5867_);
                        v___x_5869_ = l_Int_toNat(v___x_5868_);
                        leanh::lean_dec(v___x_5868_);
                        v___x_5870_ = l_Lean_instToExprInt64_mkNat(v___x_5869_);
                        v___x_5871_ =
                            l_Lean_mkApp3(v___x_5864_, v___x_5865_, v___x_5866_, v___x_5870_);
                        v___y_5583_ = v___x_5871_;
                        state = 15;
                        continue;
                    } else {
                        v___x_5872_ = lean_int64_to_int_sint(v___x_5861_);
                        v___x_5873_ = l_Int_toNat(v___x_5872_);
                        leanh::lean_dec(v___x_5872_);
                        v___x_5874_ = l_Lean_instToExprInt64_mkNat(v___x_5873_);
                        v___y_5583_ = v___x_5874_;
                        state = 15;
                        continue;
                    }
                }
            }
            39 => {
                v___x_5857_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__36);
                v___x_5858_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5858_, 0, v___x_5856_);
                leanh::lean_ctor_set(v___x_5858_, 1, v___x_5857_);
                v___x_5859_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v___x_5858_, v_a_5489_, v_a_5490_, v_a_5491_, v_a_5492_);
                return v___x_5859_;
            }
            40 => {
                if v_isShared_5880_ == 0 {
                    v___x_5882_ = v___x_5879_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_a_5877_);
                    v___x_5882_ = v_reuseFailAlloc_5883_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5882_;
            }
            42 => {
                v___x_5890_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___closed__3);
                v___x_5891_ = l_Lean_mkNatLit(v_w_5885_);
                v___x_5892_ = l_Lean_mkNatLit(v_bv_5886_);
                v___x_5893_ = l_Lean_mkAppB(v___x_5890_, v___x_5891_, v___x_5892_);
                if v_isShared_5889_ == 0 {
                    leanh::lean_ctor_set(v___x_5888_, 1, v___x_5893_);
                    leanh::lean_ctor_set(v___x_5888_, 0, v_var_5485_);
                    v___x_5895_ = v___x_5888_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_var_5485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5897_, 1, v___x_5893_);
                    v___x_5895_ = v_reuseFailAlloc_5897_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_5896_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5896_, 0, v___x_5895_);
                return v___x_5896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation___boxed(
    mut v_var_5899_: *mut leanh::LeanObject,
    mut v_value_5900_: *mut leanh::LeanObject,
    mut v_a_5901_: *mut leanh::LeanObject,
    mut v_a_5902_: *mut leanh::LeanObject,
    mut v_a_5903_: *mut leanh::LeanObject,
    mut v_a_5904_: *mut leanh::LeanObject,
    mut v_a_5905_: *mut leanh::LeanObject,
    mut v_a_5906_: *mut leanh::LeanObject,
    mut v_a_5907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5908_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_var_5899_, v_value_5900_, v_a_5901_, v_a_5902_, v_a_5903_, v_a_5904_, v_a_5905_, v_a_5906_);
    leanh::lean_dec(v_a_5906_);
    leanh::lean_dec_ref(v_a_5905_);
    leanh::lean_dec(v_a_5904_);
    leanh::lean_dec_ref(v_a_5903_);
    leanh::lean_dec(v_a_5902_);
    leanh::lean_dec_ref(v_a_5901_);
    return v_res_5908_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(
    mut v_00_u03b1_5909_: *mut leanh::LeanObject,
    mut v_msg_5910_: *mut leanh::LeanObject,
    mut v___y_5911_: *mut leanh::LeanObject,
    mut v___y_5912_: *mut leanh::LeanObject,
    mut v___y_5913_: *mut leanh::LeanObject,
    mut v___y_5914_: *mut leanh::LeanObject,
    mut v___y_5915_: *mut leanh::LeanObject,
    mut v___y_5916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5918_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___redArg(v_msg_5910_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
    return v___x_5918_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2___boxed(
    mut v_00_u03b1_5919_: *mut leanh::LeanObject,
    mut v_msg_5920_: *mut leanh::LeanObject,
    mut v___y_5921_: *mut leanh::LeanObject,
    mut v___y_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
    mut v___y_5924_: *mut leanh::LeanObject,
    mut v___y_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
    mut v___y_5927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5928_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__2(v_00_u03b1_5919_, v_msg_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
    leanh::lean_dec(v___y_5926_);
    leanh::lean_dec_ref(v___y_5925_);
    leanh::lean_dec(v___y_5924_);
    leanh::lean_dec_ref(v___y_5923_);
    leanh::lean_dec(v___y_5922_);
    leanh::lean_dec_ref(v___y_5921_);
    return v_res_5928_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(
    mut v_00_u03b1_5929_: *mut leanh::LeanObject,
    mut v_constName_5930_: *mut leanh::LeanObject,
    mut v___y_5931_: *mut leanh::LeanObject,
    mut v___y_5932_: *mut leanh::LeanObject,
    mut v___y_5933_: *mut leanh::LeanObject,
    mut v___y_5934_: *mut leanh::LeanObject,
    mut v___y_5935_: *mut leanh::LeanObject,
    mut v___y_5936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___redArg(v_constName_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_);
    return v___x_5938_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0___boxed(
    mut v_00_u03b1_5939_: *mut leanh::LeanObject,
    mut v_constName_5940_: *mut leanh::LeanObject,
    mut v___y_5941_: *mut leanh::LeanObject,
    mut v___y_5942_: *mut leanh::LeanObject,
    mut v___y_5943_: *mut leanh::LeanObject,
    mut v___y_5944_: *mut leanh::LeanObject,
    mut v___y_5945_: *mut leanh::LeanObject,
    mut v___y_5946_: *mut leanh::LeanObject,
    mut v___y_5947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5948_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0(v_00_u03b1_5939_, v_constName_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_);
    leanh::lean_dec(v___y_5946_);
    leanh::lean_dec_ref(v___y_5945_);
    leanh::lean_dec(v___y_5944_);
    leanh::lean_dec_ref(v___y_5943_);
    leanh::lean_dec(v___y_5942_);
    leanh::lean_dec_ref(v___y_5941_);
    return v_res_5948_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(
    mut v_00_u03b1_5949_: *mut leanh::LeanObject,
    mut v_ref_5950_: *mut leanh::LeanObject,
    mut v_constName_5951_: *mut leanh::LeanObject,
    mut v___y_5952_: *mut leanh::LeanObject,
    mut v___y_5953_: *mut leanh::LeanObject,
    mut v___y_5954_: *mut leanh::LeanObject,
    mut v___y_5955_: *mut leanh::LeanObject,
    mut v___y_5956_: *mut leanh::LeanObject,
    mut v___y_5957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5959_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___redArg(v_ref_5950_, v_constName_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_);
    return v___x_5959_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_5960_: *mut leanh::LeanObject,
    mut v_ref_5961_: *mut leanh::LeanObject,
    mut v_constName_5962_: *mut leanh::LeanObject,
    mut v___y_5963_: *mut leanh::LeanObject,
    mut v___y_5964_: *mut leanh::LeanObject,
    mut v___y_5965_: *mut leanh::LeanObject,
    mut v___y_5966_: *mut leanh::LeanObject,
    mut v___y_5967_: *mut leanh::LeanObject,
    mut v___y_5968_: *mut leanh::LeanObject,
    mut v___y_5969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5970_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2(v_00_u03b1_5960_, v_ref_5961_, v_constName_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_);
    leanh::lean_dec(v___y_5968_);
    leanh::lean_dec_ref(v___y_5967_);
    leanh::lean_dec(v___y_5966_);
    leanh::lean_dec_ref(v___y_5965_);
    leanh::lean_dec(v___y_5964_);
    leanh::lean_dec_ref(v___y_5963_);
    leanh::lean_dec(v_ref_5961_);
    return v_res_5970_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b1_5971_: *mut leanh::LeanObject,
    mut v_ref_5972_: *mut leanh::LeanObject,
    mut v_msg_5973_: *mut leanh::LeanObject,
    mut v_declHint_5974_: *mut leanh::LeanObject,
    mut v___y_5975_: *mut leanh::LeanObject,
    mut v___y_5976_: *mut leanh::LeanObject,
    mut v___y_5977_: *mut leanh::LeanObject,
    mut v___y_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5982_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___redArg(v_ref_5972_, v_msg_5973_, v_declHint_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_);
    return v___x_5982_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b1_5983_: *mut leanh::LeanObject,
    mut v_ref_5984_: *mut leanh::LeanObject,
    mut v_msg_5985_: *mut leanh::LeanObject,
    mut v_declHint_5986_: *mut leanh::LeanObject,
    mut v___y_5987_: *mut leanh::LeanObject,
    mut v___y_5988_: *mut leanh::LeanObject,
    mut v___y_5989_: *mut leanh::LeanObject,
    mut v___y_5990_: *mut leanh::LeanObject,
    mut v___y_5991_: *mut leanh::LeanObject,
    mut v___y_5992_: *mut leanh::LeanObject,
    mut v___y_5993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5994_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5(v_00_u03b1_5983_, v_ref_5984_, v_msg_5985_, v_declHint_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    leanh::lean_dec(v___y_5992_);
    leanh::lean_dec_ref(v___y_5991_);
    leanh::lean_dec(v___y_5990_);
    leanh::lean_dec_ref(v___y_5989_);
    leanh::lean_dec(v___y_5988_);
    leanh::lean_dec_ref(v___y_5987_);
    leanh::lean_dec(v_ref_5984_);
    return v_res_5994_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(
    mut v_msg_5995_: *mut leanh::LeanObject,
    mut v_declHint_5996_: *mut leanh::LeanObject,
    mut v___y_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
    mut v___y_6000_: *mut leanh::LeanObject,
    mut v___y_6001_: *mut leanh::LeanObject,
    mut v___y_6002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6004_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___redArg(v_msg_5995_, v_declHint_5996_, v___y_6002_);
    return v___x_6004_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7___boxed(
    mut v_msg_6005_: *mut leanh::LeanObject,
    mut v_declHint_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
    mut v___y_6009_: *mut leanh::LeanObject,
    mut v___y_6010_: *mut leanh::LeanObject,
    mut v___y_6011_: *mut leanh::LeanObject,
    mut v___y_6012_: *mut leanh::LeanObject,
    mut v___y_6013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6014_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__6_spec__7(v_msg_6005_, v_declHint_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_);
    leanh::lean_dec(v___y_6012_);
    leanh::lean_dec_ref(v___y_6011_);
    leanh::lean_dec(v___y_6010_);
    leanh::lean_dec_ref(v___y_6009_);
    leanh::lean_dec(v___y_6008_);
    leanh::lean_dec_ref(v___y_6007_);
    return v_res_6014_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(
    mut v_00_u03b1_6015_: *mut leanh::LeanObject,
    mut v_ref_6016_: *mut leanh::LeanObject,
    mut v_msg_6017_: *mut leanh::LeanObject,
    mut v___y_6018_: *mut leanh::LeanObject,
    mut v___y_6019_: *mut leanh::LeanObject,
    mut v___y_6020_: *mut leanh::LeanObject,
    mut v___y_6021_: *mut leanh::LeanObject,
    mut v___y_6022_: *mut leanh::LeanObject,
    mut v___y_6023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___redArg(v_ref_6016_, v_msg_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
    return v___x_6025_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_6026_: *mut leanh::LeanObject,
    mut v_ref_6027_: *mut leanh::LeanObject,
    mut v_msg_6028_: *mut leanh::LeanObject,
    mut v___y_6029_: *mut leanh::LeanObject,
    mut v___y_6030_: *mut leanh::LeanObject,
    mut v___y_6031_: *mut leanh::LeanObject,
    mut v___y_6032_: *mut leanh::LeanObject,
    mut v___y_6033_: *mut leanh::LeanObject,
    mut v___y_6034_: *mut leanh::LeanObject,
    mut v___y_6035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6036_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation_spec__0_spec__0_spec__2_spec__5_spec__7(v_00_u03b1_6026_, v_ref_6027_, v_msg_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
    leanh::lean_dec(v___y_6034_);
    leanh::lean_dec_ref(v___y_6033_);
    leanh::lean_dec(v___y_6032_);
    leanh::lean_dec_ref(v___y_6031_);
    leanh::lean_dec(v___y_6030_);
    leanh::lean_dec_ref(v___y_6029_);
    leanh::lean_dec(v_ref_6027_);
    return v_res_6036_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(
    mut v_a_6037_: *mut leanh::LeanObject,
    mut v_x_6038_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6039_: u8 = 0;
    let mut v_key_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6038_) == 0 {
                    v___x_6039_ = 0;
                    return v___x_6039_;
                } else {
                    v_key_6040_ = leanh::lean_ctor_get(v_x_6038_, 0);
                    v_tail_6041_ = leanh::lean_ctor_get(v_x_6038_, 2);
                    v___x_6042_ = lean_expr_eqv(v_key_6040_, v_a_6037_);
                    if v___x_6042_ == 0 {
                        v_x_6038_ = v_tail_6041_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6042_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg___boxed(
    mut v_a_6044_: *mut leanh::LeanObject,
    mut v_x_6045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6046_: u8 = 0;
    let mut v_r_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_6044_, v_x_6045_);
    leanh::lean_dec(v_x_6045_);
    leanh::lean_dec_ref(v_a_6044_);
    v_r_6047_ = leanh::lean_box((v_res_6046_) as usize);
    return v_r_6047_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_6048_: *mut leanh::LeanObject,
    mut v_x_6049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6055_: u8 = 0;
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: u64 = 0;
    let mut v___x_6058_: u64 = 0;
    let mut v___x_6059_: u64 = 0;
    let mut v_fold_6060_: u64 = 0;
    let mut v___x_6061_: u64 = 0;
    let mut v___x_6062_: u64 = 0;
    let mut v___x_6063_: u64 = 0;
    let mut v___x_6064_: usize = 0;
    let mut v___x_6065_: usize = 0;
    let mut v___x_6066_: usize = 0;
    let mut v___x_6067_: usize = 0;
    let mut v___x_6068_: usize = 0;
    let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6049_) == 0 {
                    return v_x_6048_;
                } else {
                    v_key_6050_ = leanh::lean_ctor_get(v_x_6049_, 0);
                    v_value_6051_ = leanh::lean_ctor_get(v_x_6049_, 1);
                    v_tail_6052_ = leanh::lean_ctor_get(v_x_6049_, 2);
                    v_isSharedCheck_6075_ = (!leanh::lean_is_exclusive(v_x_6049_)) as u8;
                    if v_isSharedCheck_6075_ == 0 {
                        v___x_6054_ = v_x_6049_;
                        v_isShared_6055_ = v_isSharedCheck_6075_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6052_);
                        leanh::lean_inc(v_value_6051_);
                        leanh::lean_inc(v_key_6050_);
                        leanh::lean_dec(v_x_6049_);
                        v___x_6054_ = leanh::lean_box(0);
                        v_isShared_6055_ = v_isSharedCheck_6075_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6056_ = lean_array_get_size(v_x_6048_);
                v___x_6057_ = l_Lean_Expr_hash(v_key_6050_);
                v___x_6058_ = 32u64;
                v___x_6059_ = lean_uint64_shift_right(v___x_6057_, v___x_6058_);
                v_fold_6060_ = lean_uint64_xor(v___x_6057_, v___x_6059_);
                v___x_6061_ = 16u64;
                v___x_6062_ = lean_uint64_shift_right(v_fold_6060_, v___x_6061_);
                v___x_6063_ = lean_uint64_xor(v_fold_6060_, v___x_6062_);
                v___x_6064_ = lean_uint64_to_usize(v___x_6063_);
                v___x_6065_ = lean_usize_of_nat(v___x_6056_);
                v___x_6066_ = 1usize;
                v___x_6067_ = lean_usize_sub(v___x_6065_, v___x_6066_);
                v___x_6068_ = lean_usize_land(v___x_6064_, v___x_6067_);
                v___x_6069_ = lean_array_uget_borrowed(v_x_6048_, v___x_6068_);
                leanh::lean_inc(v___x_6069_);
                if v_isShared_6055_ == 0 {
                    leanh::lean_ctor_set(v___x_6054_, 2, v___x_6069_);
                    v___x_6071_ = v___x_6054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6074_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_key_6050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6074_, 1, v_value_6051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6074_, 2, v___x_6069_);
                    v___x_6071_ = v_reuseFailAlloc_6074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6072_ = lean_array_uset(v_x_6048_, v___x_6068_, v___x_6071_);
                v_x_6048_ = v___x_6072_;
                v_x_6049_ = v_tail_6052_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(
    mut v_i_6076_: *mut leanh::LeanObject,
    mut v_source_6077_: *mut leanh::LeanObject,
    mut v_target_6078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: u8 = 0;
    let mut v_es_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6079_ = lean_array_get_size(v_source_6077_);
                v___x_6080_ = lean_nat_dec_lt(v_i_6076_, v___x_6079_);
                if v___x_6080_ == 0 {
                    leanh::lean_dec_ref(v_source_6077_);
                    leanh::lean_dec(v_i_6076_);
                    return v_target_6078_;
                } else {
                    v_es_6081_ = lean_array_fget(v_source_6077_, v_i_6076_);
                    v___x_6082_ = leanh::lean_box(0);
                    v_source_6083_ = lean_array_fset(v_source_6077_, v_i_6076_, v___x_6082_);
                    v_target_6084_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(v_target_6078_, v_es_6081_);
                    v___x_6085_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6086_ = lean_nat_add(v_i_6076_, v___x_6085_);
                    leanh::lean_dec(v_i_6076_);
                    v_i_6076_ = v___x_6086_;
                    v_source_6077_ = v_source_6083_;
                    v_target_6078_ = v_target_6084_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(
    mut v_data_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6089_ = lean_array_get_size(v_data_6088_);
    v___x_6090_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6091_ = lean_nat_mul(v___x_6089_, v___x_6090_);
    v___x_6092_ = leanh::lean_unsigned_to_nat(0);
    v___x_6093_ = leanh::lean_box(0);
    v___x_6094_ = lean_mk_array(v_nbuckets_6091_, v___x_6093_);
    v___x_6095_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(v___x_6092_, v_data_6088_, v___x_6094_);
    return v___x_6095_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(
    mut v_m_6096_: *mut leanh::LeanObject,
    mut v_a_6097_: *mut leanh::LeanObject,
    mut v_b_6098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: u64 = 0;
    let mut v___x_6103_: u64 = 0;
    let mut v___x_6104_: u64 = 0;
    let mut v_fold_6105_: u64 = 0;
    let mut v___x_6106_: u64 = 0;
    let mut v___x_6107_: u64 = 0;
    let mut v___x_6108_: u64 = 0;
    let mut v___x_6109_: usize = 0;
    let mut v___x_6110_: usize = 0;
    let mut v___x_6111_: usize = 0;
    let mut v___x_6112_: usize = 0;
    let mut v___x_6113_: usize = 0;
    let mut v_bkt_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: u8 = 0;
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6118_: u8 = 0;
    let mut v___x_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: u8 = 0;
    let mut v_val_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6136_: u8 = 0;
    let mut v_unused_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6099_ = leanh::lean_ctor_get(v_m_6096_, 0);
                v_buckets_6100_ = leanh::lean_ctor_get(v_m_6096_, 1);
                v___x_6101_ = lean_array_get_size(v_buckets_6100_);
                v___x_6102_ = l_Lean_Expr_hash(v_a_6097_);
                v___x_6103_ = 32u64;
                v___x_6104_ = lean_uint64_shift_right(v___x_6102_, v___x_6103_);
                v_fold_6105_ = lean_uint64_xor(v___x_6102_, v___x_6104_);
                v___x_6106_ = 16u64;
                v___x_6107_ = lean_uint64_shift_right(v_fold_6105_, v___x_6106_);
                v___x_6108_ = lean_uint64_xor(v_fold_6105_, v___x_6107_);
                v___x_6109_ = lean_uint64_to_usize(v___x_6108_);
                v___x_6110_ = lean_usize_of_nat(v___x_6101_);
                v___x_6111_ = 1usize;
                v___x_6112_ = lean_usize_sub(v___x_6110_, v___x_6111_);
                v___x_6113_ = lean_usize_land(v___x_6109_, v___x_6112_);
                v_bkt_6114_ = lean_array_uget_borrowed(v_buckets_6100_, v___x_6113_);
                v___x_6115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_6097_, v_bkt_6114_);
                if v___x_6115_ == 0 {
                    leanh::lean_inc_ref(v_buckets_6100_);
                    leanh::lean_inc(v_size_6099_);
                    v_isSharedCheck_6136_ = (!leanh::lean_is_exclusive(v_m_6096_)) as u8;
                    if v_isSharedCheck_6136_ == 0 {
                        v_unused_6137_ = leanh::lean_ctor_get(v_m_6096_, 1);
                        leanh::lean_dec(v_unused_6137_);
                        v_unused_6138_ = leanh::lean_ctor_get(v_m_6096_, 0);
                        leanh::lean_dec(v_unused_6138_);
                        v___x_6117_ = v_m_6096_;
                        v_isShared_6118_ = v_isSharedCheck_6136_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_6096_);
                        v___x_6117_ = leanh::lean_box(0);
                        v_isShared_6118_ = v_isSharedCheck_6136_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_6098_);
                    leanh::lean_dec_ref(v_a_6097_);
                    return v_m_6096_;
                }
            }
            1 => {
                v___x_6119_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_6120_ = lean_nat_add(v_size_6099_, v___x_6119_);
                leanh::lean_dec(v_size_6099_);
                leanh::lean_inc(v_bkt_6114_);
                v___x_6121_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6121_, 0, v_a_6097_);
                leanh::lean_ctor_set(v___x_6121_, 1, v_b_6098_);
                leanh::lean_ctor_set(v___x_6121_, 2, v_bkt_6114_);
                v_buckets_x27_6122_ = lean_array_uset(v_buckets_6100_, v___x_6113_, v___x_6121_);
                v___x_6123_ = leanh::lean_unsigned_to_nat(4);
                v___x_6124_ = lean_nat_mul(v_size_x27_6120_, v___x_6123_);
                v___x_6125_ = leanh::lean_unsigned_to_nat(3);
                v___x_6126_ = lean_nat_div(v___x_6124_, v___x_6125_);
                leanh::lean_dec(v___x_6124_);
                v___x_6127_ = lean_array_get_size(v_buckets_x27_6122_);
                v___x_6128_ = lean_nat_dec_le(v___x_6126_, v___x_6127_);
                leanh::lean_dec(v___x_6126_);
                if v___x_6128_ == 0 {
                    v_val_6129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(v_buckets_x27_6122_);
                    if v_isShared_6118_ == 0 {
                        leanh::lean_ctor_set(v___x_6117_, 1, v_val_6129_);
                        leanh::lean_ctor_set(v___x_6117_, 0, v_size_x27_6120_);
                        v___x_6131_ = v___x_6117_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_size_x27_6120_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6132_, 1, v_val_6129_);
                        v___x_6131_ = v_reuseFailAlloc_6132_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_6118_ == 0 {
                        leanh::lean_ctor_set(v___x_6117_, 1, v_buckets_x27_6122_);
                        leanh::lean_ctor_set(v___x_6117_, 0, v_size_x27_6120_);
                        v___x_6134_ = v___x_6117_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_size_x27_6120_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6135_, 1, v_buckets_x27_6122_);
                        v___x_6134_ = v_reuseFailAlloc_6135_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6131_;
            }
            3 => {
                return v___x_6134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(
    mut v_as_6139_: *mut leanh::LeanObject,
    mut v_sz_6140_: usize,
    mut v_i_6141_: usize,
    mut v_b_6142_: *mut leanh::LeanObject,
    mut v___y_6143_: *mut leanh::LeanObject,
    mut v___y_6144_: *mut leanh::LeanObject,
    mut v___y_6145_: *mut leanh::LeanObject,
    mut v___y_6146_: *mut leanh::LeanObject,
    mut v___y_6147_: *mut leanh::LeanObject,
    mut v___y_6148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: usize = 0;
    let mut v___x_6153_: usize = 0;
    let mut v___x_6155_: u8 = 0;
    let mut v___x_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6169_: u8 = 0;
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6183_: u8 = 0;
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6189_: u8 = 0;
    let mut v_reuseFailAlloc_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6191_: u8 = 0;
    let mut v_a_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6155_ = lean_usize_dec_lt(v_i_6141_, v_sz_6140_);
                if v___x_6155_ == 0 {
                    v___x_6156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6156_, 0, v_b_6142_);
                    return v___x_6156_;
                } else {
                    v_a_6157_ = lean_array_uget_borrowed(v_as_6139_, v_i_6141_);
                    v_fst_6158_ = leanh::lean_ctor_get(v_a_6157_, 0);
                    v_snd_6159_ = leanh::lean_ctor_get(v_a_6157_, 1);
                    leanh::lean_inc(v_snd_6159_);
                    leanh::lean_inc(v_fst_6158_);
                    v___x_6160_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_transformEquation(v_fst_6158_, v_snd_6159_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
                    if leanh::lean_obj_tag(v___x_6160_) == 0 {
                        v_a_6161_ = leanh::lean_ctor_get(v___x_6160_, 0);
                        leanh::lean_inc(v_a_6161_);
                        leanh::lean_dec_ref_known(v___x_6160_, 1);
                        v_fst_6162_ = leanh::lean_ctor_get(v_a_6161_, 0);
                        leanh::lean_inc(v_fst_6162_);
                        v___x_6163_ = lean_st_ref_take(v___y_6144_);
                        v_uninterpretedSymbols_6164_ = leanh::lean_ctor_get(v___x_6163_, 0);
                        v_unusedRelevantHypotheses_6165_ =
                            leanh::lean_ctor_get(v___x_6163_, 1);
                        v_derivedEquations_6166_ = leanh::lean_ctor_get(v___x_6163_, 2);
                        v_isSharedCheck_6191_ =
                            (!leanh::lean_is_exclusive(v___x_6163_)) as u8;
                        if v_isSharedCheck_6191_ == 0 {
                            v___x_6168_ = v___x_6163_;
                            v_isShared_6169_ = v_isSharedCheck_6191_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_derivedEquations_6166_);
                            leanh::lean_inc(v_unusedRelevantHypotheses_6165_);
                            leanh::lean_inc(v_uninterpretedSymbols_6164_);
                            leanh::lean_dec(v___x_6163_);
                            v___x_6168_ = leanh::lean_box(0);
                            v_isShared_6169_ = v_isSharedCheck_6191_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_6192_ = leanh::lean_ctor_get(v___x_6160_, 0);
                        v_isSharedCheck_6199_ =
                            (!leanh::lean_is_exclusive(v___x_6160_)) as u8;
                        if v_isSharedCheck_6199_ == 0 {
                            v___x_6194_ = v___x_6160_;
                            v_isShared_6195_ = v_isSharedCheck_6199_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6192_);
                            leanh::lean_dec(v___x_6160_);
                            v___x_6194_ = leanh::lean_box(0);
                            v_isShared_6195_ = v_isSharedCheck_6199_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6152_ = 1usize;
                v___x_6153_ = lean_usize_add(v_i_6141_, v___x_6152_);
                v_i_6141_ = v___x_6153_;
                v_b_6142_ = v_a_6151_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6170_ = lean_array_push(v_derivedEquations_6166_, v_a_6161_);
                if v_isShared_6169_ == 0 {
                    leanh::lean_ctor_set(v___x_6168_, 2, v___x_6170_);
                    v___x_6172_ = v___x_6168_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6190_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6190_,
                        0,
                        v_uninterpretedSymbols_6164_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6190_,
                        1,
                        v_unusedRelevantHypotheses_6165_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6190_, 2, v___x_6170_);
                    v___x_6172_ = v_reuseFailAlloc_6190_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6173_ = lean_st_ref_set(v___y_6144_, v___x_6172_);
                v___x_6174_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_fst_6162_) == 1 {
                    v_fvarId_6175_ = leanh::lean_ctor_get(v_fst_6162_, 0);
                    leanh::lean_inc(v_fvarId_6175_);
                    leanh::lean_dec_ref_known(v_fst_6162_, 1);
                    v___x_6176_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_checkRelevantHypsUsed(v_fvarId_6175_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
                    leanh::lean_dec(v_fvarId_6175_);
                    if leanh::lean_obj_tag(v___x_6176_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6176_, 1);
                        v_a_6151_ = v___x_6174_;
                        state = 1;
                        continue;
                    } else {
                        return v___x_6176_;
                    }
                } else {
                    v___x_6177_ = lean_st_ref_take(v___y_6144_);
                    v_uninterpretedSymbols_6178_ = leanh::lean_ctor_get(v___x_6177_, 0);
                    v_unusedRelevantHypotheses_6179_ = leanh::lean_ctor_get(v___x_6177_, 1);
                    v_derivedEquations_6180_ = leanh::lean_ctor_get(v___x_6177_, 2);
                    v_isSharedCheck_6189_ = (!leanh::lean_is_exclusive(v___x_6177_)) as u8;
                    if v_isSharedCheck_6189_ == 0 {
                        v___x_6182_ = v___x_6177_;
                        v_isShared_6183_ = v_isSharedCheck_6189_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_derivedEquations_6180_);
                        leanh::lean_inc(v_unusedRelevantHypotheses_6179_);
                        leanh::lean_inc(v_uninterpretedSymbols_6178_);
                        leanh::lean_dec(v___x_6177_);
                        v___x_6182_ = leanh::lean_box(0);
                        v_isShared_6183_ = v_isSharedCheck_6189_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6184_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_uninterpretedSymbols_6178_, v_fst_6162_, v___x_6174_);
                if v_isShared_6183_ == 0 {
                    leanh::lean_ctor_set(v___x_6182_, 0, v___x_6184_);
                    v___x_6186_ = v___x_6182_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6188_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6188_, 0, v___x_6184_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6188_,
                        1,
                        v_unusedRelevantHypotheses_6179_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6188_,
                        2,
                        v_derivedEquations_6180_,
                    );
                    v___x_6186_ = v_reuseFailAlloc_6188_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6187_ = lean_st_ref_set(v___y_6144_, v___x_6186_);
                v_a_6151_ = v___x_6174_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6195_ == 0 {
                    v___x_6197_ = v___x_6194_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
                    v___x_6197_ = v_reuseFailAlloc_6198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1___boxed(
    mut v_as_6200_: *mut leanh::LeanObject,
    mut v_sz_6201_: *mut leanh::LeanObject,
    mut v_i_6202_: *mut leanh::LeanObject,
    mut v_b_6203_: *mut leanh::LeanObject,
    mut v___y_6204_: *mut leanh::LeanObject,
    mut v___y_6205_: *mut leanh::LeanObject,
    mut v___y_6206_: *mut leanh::LeanObject,
    mut v___y_6207_: *mut leanh::LeanObject,
    mut v___y_6208_: *mut leanh::LeanObject,
    mut v___y_6209_: *mut leanh::LeanObject,
    mut v___y_6210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6211_: usize = 0;
    let mut v_i_boxed_6212_: usize = 0;
    let mut v_res_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6211_ = leanh::lean_unbox_usize(v_sz_6201_);
    leanh::lean_dec(v_sz_6201_);
    v_i_boxed_6212_ = leanh::lean_unbox_usize(v_i_6202_);
    leanh::lean_dec(v_i_6202_);
    v_res_6213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_as_6200_, v_sz_boxed_6211_, v_i_boxed_6212_, v_b_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_);
    leanh::lean_dec(v___y_6209_);
    leanh::lean_dec_ref(v___y_6208_);
    leanh::lean_dec(v___y_6207_);
    leanh::lean_dec_ref(v___y_6206_);
    leanh::lean_dec(v___y_6205_);
    leanh::lean_dec_ref(v___y_6204_);
    leanh::lean_dec_ref(v_as_6200_);
    return v_res_6213_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(
    mut v_a_6214_: *mut leanh::LeanObject,
    mut v_a_6215_: *mut leanh::LeanObject,
    mut v_a_6216_: *mut leanh::LeanObject,
    mut v_a_6217_: *mut leanh::LeanObject,
    mut v_a_6218_: *mut leanh::LeanObject,
    mut v_a_6219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_equations_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6223_: usize = 0;
    let mut v___x_6224_: usize = 0;
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6228_: u8 = 0;
    let mut v___x_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6232_: u8 = 0;
    let mut v_unused_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_equations_6221_ = leanh::lean_ctor_get(v_a_6214_, 2);
                v___x_6222_ = leanh::lean_box(0);
                v_sz_6223_ = lean_array_size(v_equations_6221_);
                v___x_6224_ = 0usize;
                v___x_6225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__1(v_equations_6221_, v_sz_6223_, v___x_6224_, v___x_6222_, v_a_6214_, v_a_6215_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_);
                if leanh::lean_obj_tag(v___x_6225_) == 0 {
                    v_isSharedCheck_6232_ = (!leanh::lean_is_exclusive(v___x_6225_)) as u8;
                    if v_isSharedCheck_6232_ == 0 {
                        v_unused_6233_ = leanh::lean_ctor_get(v___x_6225_, 0);
                        leanh::lean_dec(v_unused_6233_);
                        v___x_6227_ = v___x_6225_;
                        v_isShared_6228_ = v_isSharedCheck_6232_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6225_);
                        v___x_6227_ = leanh::lean_box(0);
                        v_isShared_6228_ = v_isSharedCheck_6232_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_6225_;
                }
            }
            1 => {
                if v_isShared_6228_ == 0 {
                    leanh::lean_ctor_set(v___x_6227_, 0, v___x_6222_);
                    v___x_6230_ = v___x_6227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6231_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6231_, 0, v___x_6222_);
                    v___x_6230_ = v_reuseFailAlloc_6231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed(
    mut v_a_6234_: *mut leanh::LeanObject,
    mut v_a_6235_: *mut leanh::LeanObject,
    mut v_a_6236_: *mut leanh::LeanObject,
    mut v_a_6237_: *mut leanh::LeanObject,
    mut v_a_6238_: *mut leanh::LeanObject,
    mut v_a_6239_: *mut leanh::LeanObject,
    mut v_a_6240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6241_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose(v_a_6234_, v_a_6235_, v_a_6236_, v_a_6237_, v_a_6238_, v_a_6239_);
    leanh::lean_dec(v_a_6239_);
    leanh::lean_dec_ref(v_a_6238_);
    leanh::lean_dec(v_a_6237_);
    leanh::lean_dec_ref(v_a_6236_);
    leanh::lean_dec(v_a_6235_);
    leanh::lean_dec_ref(v_a_6234_);
    return v_res_6241_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0(
    mut v_00_u03b2_6242_: *mut leanh::LeanObject,
    mut v_m_6243_: *mut leanh::LeanObject,
    mut v_a_6244_: *mut leanh::LeanObject,
    mut v_b_6245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6246_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0___redArg(v_m_6243_, v_a_6244_, v_b_6245_);
    return v___x_6246_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(
    mut v_00_u03b2_6247_: *mut leanh::LeanObject,
    mut v_a_6248_: *mut leanh::LeanObject,
    mut v_x_6249_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6250_: u8 = 0;
    v___x_6250_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___redArg(v_a_6248_, v_x_6249_);
    return v___x_6250_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0___boxed(
    mut v_00_u03b2_6251_: *mut leanh::LeanObject,
    mut v_a_6252_: *mut leanh::LeanObject,
    mut v_x_6253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6254_: u8 = 0;
    let mut v_r_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__0(v_00_u03b2_6251_, v_a_6252_, v_x_6253_);
    leanh::lean_dec(v_x_6253_);
    leanh::lean_dec_ref(v_a_6252_);
    v_r_6255_ = leanh::lean_box((v_res_6254_) as usize);
    return v_r_6255_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1(
    mut v_00_u03b2_6256_: *mut leanh::LeanObject,
    mut v_data_6257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1___redArg(v_data_6257_);
    return v___x_6258_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2(
    mut v_00_u03b2_6259_: *mut leanh::LeanObject,
    mut v_i_6260_: *mut leanh::LeanObject,
    mut v_source_6261_: *mut leanh::LeanObject,
    mut v_target_6262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6263_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2___redArg(v_i_6260_, v_source_6261_, v_target_6262_);
    return v___x_6263_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_6264_: *mut leanh::LeanObject,
    mut v_x_6265_: *mut leanh::LeanObject,
    mut v_x_6266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6267_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose_spec__0_spec__1_spec__2_spec__4___redArg(v_x_6265_, v_x_6266_);
    return v___x_6267_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(
    mut v_x_6268_: *mut leanh::LeanObject,
    mut v_x_6269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6269_) == 0 {
        leanh::lean_inc(v_x_6268_);
        return v_x_6268_;
    } else {
        let mut v_key_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_6270_ = leanh::lean_ctor_get(v_x_6269_, 0);
        v_tail_6271_ = leanh::lean_ctor_get(v_x_6269_, 2);
        v___x_6272_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_x_6268_, v_tail_6271_);
        leanh::lean_inc(v_key_6270_);
        v___x_6273_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6273_, 0, v_key_6270_);
        leanh::lean_ctor_set(v___x_6273_, 1, v___x_6272_);
        return v___x_6273_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1___boxed(
    mut v_x_6274_: *mut leanh::LeanObject,
    mut v_x_6275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6276_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_x_6274_, v_x_6275_);
    leanh::lean_dec(v_x_6275_);
    leanh::lean_dec(v_x_6274_);
    return v_res_6276_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(
    mut v_as_6277_: *mut leanh::LeanObject,
    mut v_i_6278_: usize,
    mut v_stop_6279_: usize,
    mut v_b_6280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6281_: u8 = 0;
    let mut v___x_6282_: usize = 0;
    let mut v___x_6283_: usize = 0;
    let mut v___x_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6281_ = lean_usize_dec_eq(v_i_6278_, v_stop_6279_);
                if v___x_6281_ == 0 {
                    v___x_6282_ = 1usize;
                    v___x_6283_ = lean_usize_sub(v_i_6278_, v___x_6282_);
                    v___x_6284_ = lean_array_uget_borrowed(v_as_6277_, v___x_6283_);
                    v___x_6285_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__1(v_b_6280_, v___x_6284_);
                    leanh::lean_dec(v_b_6280_);
                    v_i_6278_ = v___x_6283_;
                    v_b_6280_ = v___x_6285_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6280_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2___boxed(
    mut v_as_6287_: *mut leanh::LeanObject,
    mut v_i_6288_: *mut leanh::LeanObject,
    mut v_stop_6289_: *mut leanh::LeanObject,
    mut v_b_6290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6291_: usize = 0;
    let mut v_stop_boxed_6292_: usize = 0;
    let mut v_res_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6291_ = leanh::lean_unbox_usize(v_i_6288_);
    leanh::lean_dec(v_i_6288_);
    v_stop_boxed_6292_ = leanh::lean_unbox_usize(v_stop_6289_);
    leanh::lean_dec(v_stop_6289_);
    v_res_6293_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(v_as_6287_, v_i_boxed_6291_, v_stop_boxed_6292_, v_b_6290_);
    leanh::lean_dec_ref(v_as_6287_);
    return v_res_6293_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(
    mut v_a_6294_: *mut leanh::LeanObject,
    mut v_a_6295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6301_: u8 = 0;
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6294_) == 0 {
                    v___x_6296_ = l_List_reverse___redArg(v_a_6295_);
                    return v___x_6296_;
                } else {
                    v_head_6297_ = leanh::lean_ctor_get(v_a_6294_, 0);
                    v_tail_6298_ = leanh::lean_ctor_get(v_a_6294_, 1);
                    v_isSharedCheck_6307_ = (!leanh::lean_is_exclusive(v_a_6294_)) as u8;
                    if v_isSharedCheck_6307_ == 0 {
                        v___x_6300_ = v_a_6294_;
                        v_isShared_6301_ = v_isSharedCheck_6307_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6298_);
                        leanh::lean_inc(v_head_6297_);
                        leanh::lean_dec(v_a_6294_);
                        v___x_6300_ = leanh::lean_box(0);
                        v_isShared_6301_ = v_isSharedCheck_6307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6302_ = l_Lean_MessageData_ofExpr(v_head_6297_);
                if v_isShared_6301_ == 0 {
                    leanh::lean_ctor_set(v___x_6300_, 1, v_a_6295_);
                    leanh::lean_ctor_set(v___x_6300_, 0, v___x_6302_);
                    v___x_6304_ = v___x_6300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6306_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6306_, 0, v___x_6302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6306_, 1, v_a_6295_);
                    v___x_6304_ = v_reuseFailAlloc_6306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6294_ = v_tail_6298_;
                v_a_6295_ = v___x_6304_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6309_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__0;
    v___x_6310_ = l_Lean_stringToMessageData(v___x_6309_);
    return v___x_6310_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(
    mut v_d_6311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninterpretedSymbols_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: u8 = 0;
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: u8 = 0;
    let mut v___x_6328_: usize = 0;
    let mut v___x_6329_: usize = 0;
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uninterpretedSymbols_6320_ = leanh::lean_ctor_get(v_d_6311_, 0);
                v_size_6321_ = leanh::lean_ctor_get(v_uninterpretedSymbols_6320_, 0);
                v_buckets_6322_ = leanh::lean_ctor_get(v_uninterpretedSymbols_6320_, 1);
                v___x_6323_ = leanh::lean_unsigned_to_nat(0);
                v___x_6324_ = lean_nat_dec_eq(v_size_6321_, v___x_6323_);
                if v___x_6324_ == 0 {
                    v___x_6325_ = leanh::lean_box(0);
                    v___x_6326_ = lean_array_get_size(v_buckets_6322_);
                    v___x_6327_ = lean_nat_dec_lt(v___x_6323_, v___x_6326_);
                    if v___x_6327_ == 0 {
                        v___y_6313_ = v___x_6325_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6328_ = lean_usize_of_nat(v___x_6326_);
                        v___x_6329_ = 0usize;
                        v___x_6330_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__2(v_buckets_6322_, v___x_6328_, v___x_6329_, v___x_6325_);
                        v___y_6313_ = v___x_6330_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6331_ = leanh::lean_box(0);
                    return v___x_6331_;
                }
            }
            1 => {
                v___x_6314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___closed__1);
                v___x_6315_ = leanh::lean_box(0);
                v___x_6316_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v___y_6313_, v___x_6315_);
                v___x_6317_ = l_Lean_MessageData_ofList(v___x_6316_);
                v___x_6318_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6318_, 0, v___x_6314_);
                leanh::lean_ctor_set(v___x_6318_, 1, v___x_6317_);
                v___x_6319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6319_, 0, v___x_6318_);
                return v___x_6319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer___boxed(
    mut v_d_6332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6333_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer(v_d_6332_);
    leanh::lean_dec_ref(v_d_6332_);
    return v_res_6333_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(
    mut v_a_6334_: *mut leanh::LeanObject,
    mut v_a_6335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6341_: u8 = 0;
    let mut v___x_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6334_) == 0 {
                    v___x_6336_ = l_List_reverse___redArg(v_a_6335_);
                    return v___x_6336_;
                } else {
                    v_head_6337_ = leanh::lean_ctor_get(v_a_6334_, 0);
                    v_tail_6338_ = leanh::lean_ctor_get(v_a_6334_, 1);
                    v_isSharedCheck_6347_ = (!leanh::lean_is_exclusive(v_a_6334_)) as u8;
                    if v_isSharedCheck_6347_ == 0 {
                        v___x_6340_ = v_a_6334_;
                        v_isShared_6341_ = v_isSharedCheck_6347_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6338_);
                        leanh::lean_inc(v_head_6337_);
                        leanh::lean_dec(v_a_6334_);
                        v___x_6340_ = leanh::lean_box(0);
                        v_isShared_6341_ = v_isSharedCheck_6347_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6342_ = l_Lean_mkFVar(v_head_6337_);
                if v_isShared_6341_ == 0 {
                    leanh::lean_ctor_set(v___x_6340_, 1, v_a_6335_);
                    leanh::lean_ctor_set(v___x_6340_, 0, v___x_6342_);
                    v___x_6344_ = v___x_6340_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6346_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6346_, 0, v___x_6342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6346_, 1, v_a_6335_);
                    v___x_6344_ = v_reuseFailAlloc_6346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6334_ = v_tail_6338_;
                v_a_6335_ = v___x_6344_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(
    mut v_x_6348_: *mut leanh::LeanObject,
    mut v_x_6349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6349_) == 0 {
        leanh::lean_inc(v_x_6348_);
        return v_x_6348_;
    } else {
        let mut v_key_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_key_6350_ = leanh::lean_ctor_get(v_x_6349_, 0);
        v_tail_6351_ = leanh::lean_ctor_get(v_x_6349_, 2);
        v___x_6352_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_6348_, v_tail_6351_);
        leanh::lean_inc(v_key_6350_);
        v___x_6353_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6353_, 0, v_key_6350_);
        leanh::lean_ctor_set(v___x_6353_, 1, v___x_6352_);
        return v___x_6353_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1___boxed(
    mut v_x_6354_: *mut leanh::LeanObject,
    mut v_x_6355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6356_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_x_6354_, v_x_6355_);
    leanh::lean_dec(v_x_6355_);
    leanh::lean_dec(v_x_6354_);
    return v_res_6356_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(
    mut v_as_6357_: *mut leanh::LeanObject,
    mut v_i_6358_: usize,
    mut v_stop_6359_: usize,
    mut v_b_6360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6361_: u8 = 0;
    let mut v___x_6362_: usize = 0;
    let mut v___x_6363_: usize = 0;
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6361_ = lean_usize_dec_eq(v_i_6358_, v_stop_6359_);
                if v___x_6361_ == 0 {
                    v___x_6362_ = 1usize;
                    v___x_6363_ = lean_usize_sub(v_i_6358_, v___x_6362_);
                    v___x_6364_ = lean_array_uget_borrowed(v_as_6357_, v___x_6363_);
                    v___x_6365_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__1(v_b_6360_, v___x_6364_);
                    leanh::lean_dec(v_b_6360_);
                    v_i_6358_ = v___x_6363_;
                    v_b_6360_ = v___x_6365_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6360_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2___boxed(
    mut v_as_6367_: *mut leanh::LeanObject,
    mut v_i_6368_: *mut leanh::LeanObject,
    mut v_stop_6369_: *mut leanh::LeanObject,
    mut v_b_6370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6371_: usize = 0;
    let mut v_stop_boxed_6372_: usize = 0;
    let mut v_res_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6371_ = leanh::lean_unbox_usize(v_i_6368_);
    leanh::lean_dec(v_i_6368_);
    v_stop_boxed_6372_ = leanh::lean_unbox_usize(v_stop_6369_);
    leanh::lean_dec(v_stop_6369_);
    v_res_6373_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_as_6367_, v_i_boxed_6371_, v_stop_boxed_6372_, v_b_6370_);
    leanh::lean_dec_ref(v_as_6367_);
    return v_res_6373_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6375_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__0;
    v___x_6376_ = l_Lean_stringToMessageData(v___x_6375_);
    return v___x_6376_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(
    mut v_d_6377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unusedRelevantHypotheses_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: u8 = 0;
    let mut v___x_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: u8 = 0;
    let mut v___x_6395_: usize = 0;
    let mut v___x_6396_: usize = 0;
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unusedRelevantHypotheses_6387_ = leanh::lean_ctor_get(v_d_6377_, 1);
                v_size_6388_ = leanh::lean_ctor_get(v_unusedRelevantHypotheses_6387_, 0);
                v_buckets_6389_ = leanh::lean_ctor_get(v_unusedRelevantHypotheses_6387_, 1);
                v___x_6390_ = leanh::lean_unsigned_to_nat(0);
                v___x_6391_ = lean_nat_dec_eq(v_size_6388_, v___x_6390_);
                if v___x_6391_ == 0 {
                    v___x_6392_ = leanh::lean_box(0);
                    v___x_6393_ = lean_array_get_size(v_buckets_6389_);
                    v___x_6394_ = lean_nat_dec_lt(v___x_6390_, v___x_6393_);
                    if v___x_6394_ == 0 {
                        v___y_6379_ = v___x_6392_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6395_ = lean_usize_of_nat(v___x_6393_);
                        v___x_6396_ = 0usize;
                        v___x_6397_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__2(v_buckets_6389_, v___x_6395_, v___x_6396_, v___x_6392_);
                        v___y_6379_ = v___x_6397_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6398_ = leanh::lean_box(0);
                    return v___x_6398_;
                }
            }
            1 => {
                v___x_6380_ = leanh::lean_box(0);
                v___x_6381_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer_spec__0(v___y_6379_, v___x_6380_);
                v___x_6382_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___closed__1);
                v___x_6383_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_uninterpretedExplainer_spec__0(v___x_6381_, v___x_6380_);
                v___x_6384_ = l_Lean_MessageData_ofList(v___x_6383_);
                v___x_6385_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6385_, 0, v___x_6382_);
                leanh::lean_ctor_set(v___x_6385_, 1, v___x_6384_);
                v___x_6386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6386_, 0, v___x_6385_);
                return v___x_6386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer___boxed(
    mut v_d_6399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6400_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_unusedRelevantHypothesesExplainer(v_d_6399_);
    leanh::lean_dec_ref(v_d_6399_);
    return v_res_6400_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__0;
    v___x_6412_ = l_Lean_stringToMessageData(v___x_6411_);
    return v___x_6412_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__2;
    v___x_6415_ = l_Lean_stringToMessageData(v___x_6414_);
    return v___x_6415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(
    mut v_as_6416_: *mut leanh::LeanObject,
    mut v_i_6417_: usize,
    mut v_stop_6418_: usize,
    mut v_b_6419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6420_: u8 = 0;
    let mut v___x_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: usize = 0;
    let mut v___x_6428_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6420_ = lean_usize_dec_eq(v_i_6417_, v_stop_6418_);
                if v___x_6420_ == 0 {
                    v___x_6421_ = lean_array_uget_borrowed(v_as_6416_, v_i_6417_);
                    v___x_6422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__1);
                    v___x_6423_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6423_, 0, v_b_6419_);
                    leanh::lean_ctor_set(v___x_6423_, 1, v___x_6422_);
                    leanh::lean_inc(v___x_6421_);
                    v___x_6424_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6424_, 0, v___x_6423_);
                    leanh::lean_ctor_set(v___x_6424_, 1, v___x_6421_);
                    v___x_6425_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
                    v___x_6426_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6426_, 0, v___x_6424_);
                    leanh::lean_ctor_set(v___x_6426_, 1, v___x_6425_);
                    v___x_6427_ = 1usize;
                    v___x_6428_ = lean_usize_add(v_i_6417_, v___x_6427_);
                    v_i_6417_ = v___x_6428_;
                    v_b_6419_ = v___x_6426_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___boxed(
    mut v_as_6430_: *mut leanh::LeanObject,
    mut v_i_6431_: *mut leanh::LeanObject,
    mut v_stop_6432_: *mut leanh::LeanObject,
    mut v_b_6433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6434_: usize = 0;
    let mut v_stop_boxed_6435_: usize = 0;
    let mut v_res_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6434_ = leanh::lean_unbox_usize(v_i_6431_);
    leanh::lean_dec(v_i_6431_);
    v_stop_boxed_6435_ = leanh::lean_unbox_usize(v_stop_6432_);
    leanh::lean_dec(v_stop_6432_);
    v_res_6436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v_as_6430_, v_i_boxed_6434_, v_stop_boxed_6435_, v_b_6433_);
    leanh::lean_dec_ref(v_as_6430_);
    return v_res_6436_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__0;
    v___x_6439_ = l_Lean_stringToMessageData(v___x_6438_);
    return v___x_6439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(
    mut v_as_6440_: *mut leanh::LeanObject,
    mut v_i_6441_: usize,
    mut v_stop_6442_: usize,
    mut v_b_6443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6444_: u8 = 0;
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: usize = 0;
    let mut v___x_6461_: usize = 0;
    let mut v_reuseFailAlloc_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6444_ = lean_usize_dec_eq(v_i_6441_, v_stop_6442_);
                if v___x_6444_ == 0 {
                    v___x_6445_ = lean_array_uget(v_as_6440_, v_i_6441_);
                    v_fst_6446_ = leanh::lean_ctor_get(v___x_6445_, 0);
                    v_snd_6447_ = leanh::lean_ctor_get(v___x_6445_, 1);
                    v_isSharedCheck_6464_ = (!leanh::lean_is_exclusive(v___x_6445_)) as u8;
                    if v_isSharedCheck_6464_ == 0 {
                        v___x_6449_ = v___x_6445_;
                        v_isShared_6450_ = v_isSharedCheck_6464_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6447_);
                        leanh::lean_inc(v_fst_6446_);
                        leanh::lean_dec(v___x_6445_);
                        v___x_6449_ = leanh::lean_box(0);
                        v_isShared_6450_ = v_isSharedCheck_6464_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6443_;
                }
            }
            1 => {
                v___x_6451_ = l_Lean_MessageData_ofExpr(v_fst_6446_);
                v___x_6452_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___closed__1);
                if v_isShared_6450_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6449_, 7);
                    leanh::lean_ctor_set(v___x_6449_, 1, v___x_6452_);
                    leanh::lean_ctor_set(v___x_6449_, 0, v___x_6451_);
                    v___x_6454_ = v___x_6449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6463_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6463_, 0, v___x_6451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6463_, 1, v___x_6452_);
                    v___x_6454_ = v_reuseFailAlloc_6463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6455_ = l_Lean_MessageData_ofExpr(v_snd_6447_);
                v___x_6456_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6456_, 0, v___x_6454_);
                leanh::lean_ctor_set(v___x_6456_, 1, v___x_6455_);
                v___x_6457_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2___closed__3);
                v___x_6458_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6458_, 0, v___x_6456_);
                leanh::lean_ctor_set(v___x_6458_, 1, v___x_6457_);
                v___x_6459_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6459_, 0, v_b_6443_);
                leanh::lean_ctor_set(v___x_6459_, 1, v___x_6458_);
                v___x_6460_ = 1usize;
                v___x_6461_ = lean_usize_add(v_i_6441_, v___x_6460_);
                v_i_6441_ = v___x_6461_;
                v_b_6443_ = v___x_6459_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0___boxed(
    mut v_as_6465_: *mut leanh::LeanObject,
    mut v_i_6466_: *mut leanh::LeanObject,
    mut v_stop_6467_: *mut leanh::LeanObject,
    mut v_b_6468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6469_: usize = 0;
    let mut v_stop_boxed_6470_: usize = 0;
    let mut v_res_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6469_ = leanh::lean_unbox_usize(v_i_6466_);
    leanh::lean_dec(v_i_6466_);
    v_stop_boxed_6470_ = leanh::lean_unbox_usize(v_stop_6467_);
    leanh::lean_dec(v_stop_6467_);
    v_res_6471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_as_6465_, v_i_boxed_6469_, v_stop_boxed_6470_, v_b_6468_);
    leanh::lean_dec_ref(v_as_6465_);
    return v_res_6471_;
}
pub unsafe fn l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(
    mut v_a_6472_: *mut leanh::LeanObject,
    mut v_x_6473_: *mut leanh::LeanObject,
    mut v_x_6474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6474_) == 0 {
                    leanh::lean_dec_ref(v_a_6472_);
                    return v_x_6473_;
                } else {
                    v_head_6475_ = leanh::lean_ctor_get(v_x_6474_, 0);
                    leanh::lean_inc(v_head_6475_);
                    v_tail_6476_ = leanh::lean_ctor_get(v_x_6474_, 1);
                    leanh::lean_inc(v_tail_6476_);
                    leanh::lean_dec_ref_known(v_x_6474_, 2);
                    leanh::lean_inc_ref(v_a_6472_);
                    v___x_6477_ = leanh::lean_apply_1(v_head_6475_, v_a_6472_);
                    if leanh::lean_obj_tag(v___x_6477_) == 1 {
                        v_val_6478_ = leanh::lean_ctor_get(v___x_6477_, 0);
                        leanh::lean_inc(v_val_6478_);
                        leanh::lean_dec_ref_known(v___x_6477_, 1);
                        v___x_6479_ = lean_array_push(v_x_6473_, v_val_6478_);
                        v_x_6473_ = v___x_6479_;
                        v_x_6474_ = v_tail_6476_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6477_);
                        v_x_6474_ = v_tail_6476_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6485_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__1;
    v___x_6486_ = l_Lean_stringToMessageData(v___x_6485_);
    return v___x_6486_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6488_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__3;
    v___x_6489_ = l_Lean_stringToMessageData(v___x_6488_);
    return v___x_6489_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__4,
    );
    v___x_6491_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2,
    );
    v___x_6492_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6492_, 0, v___x_6491_);
    leanh::lean_ctor_set(v___x_6492_, 1, v___x_6490_);
    return v___x_6492_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6494_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__6;
    v___x_6495_ = l_Lean_stringToMessageData(v___x_6494_);
    return v___x_6495_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6497_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__8;
    v___x_6498_ = l_Lean_stringToMessageData(v___x_6497_);
    return v___x_6498_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6499_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__9,
    );
    v___x_6500_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2,
    );
    v___x_6501_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6501_, 0, v___x_6500_);
    leanh::lean_ctor_set(v___x_6501_, 1, v___x_6499_);
    return v___x_6501_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(
    mut v_counterExample_6502_: *mut leanh::LeanObject,
    mut v_a_6503_: *mut leanh::LeanObject,
    mut v_a_6504_: *mut leanh::LeanObject,
    mut v_a_6505_: *mut leanh::LeanObject,
    mut v_a_6506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6513_: u8 = 0;
    let mut v_err_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_derivedEquations_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: u8 = 0;
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: usize = 0;
    let mut v___x_6528_: usize = 0;
    let mut v___x_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: usize = 0;
    let mut v___x_6534_: usize = 0;
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: u8 = 0;
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: u8 = 0;
    let mut v___x_6554_: usize = 0;
    let mut v___x_6555_: usize = 0;
    let mut v___x_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: usize = 0;
    let mut v___x_6558_: usize = 0;
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6561_: u8 = 0;
    let mut v_a_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6565_: u8 = 0;
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6508_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_diagnose___boxed as *mut core::ffi::c_void, 7, 0);
                v___x_6509_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_DiagnosisM_run(v___x_6508_, v_counterExample_6502_, v_a_6503_, v_a_6504_, v_a_6505_, v_a_6506_);
                if leanh::lean_obj_tag(v___x_6509_) == 0 {
                    v_a_6510_ = leanh::lean_ctor_get(v___x_6509_, 0);
                    v_isSharedCheck_6561_ = (!leanh::lean_is_exclusive(v___x_6509_)) as u8;
                    if v_isSharedCheck_6561_ == 0 {
                        v___x_6512_ = v___x_6509_;
                        v_isShared_6513_ = v_isSharedCheck_6561_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6510_);
                        leanh::lean_dec(v___x_6509_);
                        v___x_6512_ = leanh::lean_box(0);
                        v_isShared_6513_ = v_isSharedCheck_6561_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6562_ = leanh::lean_ctor_get(v___x_6509_, 0);
                    v_isSharedCheck_6569_ = (!leanh::lean_is_exclusive(v___x_6509_)) as u8;
                    if v_isSharedCheck_6569_ == 0 {
                        v___x_6564_ = v___x_6509_;
                        v_isShared_6565_ = v_isSharedCheck_6569_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6562_);
                        leanh::lean_dec(v___x_6509_);
                        v___x_6564_ = leanh::lean_box(0);
                        v_isShared_6565_ = v_isSharedCheck_6569_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6539_ = leanh::lean_unsigned_to_nat(0);
                v___x_6540_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__0;
                v___x_6541_ = l___private_Lean_Meta_Tactic_BVDecide_Counterexample_0__Lean_Meta_Tactic_BVDecide_explainers;
                leanh::lean_inc(v_a_6510_);
                v___x_6542_ = l_List_foldl___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__1(v_a_6510_, v___x_6540_, v___x_6541_);
                v___x_6543_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__2,
                );
                v___x_6544_ = lean_array_get_size(v___x_6542_);
                v___x_6545_ = lean_nat_dec_eq(v___x_6544_, v___x_6539_);
                if v___x_6545_ == 0 {
                    v___x_6546_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5_once), _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__5);
                    v___x_6552_ = lean_nat_dec_lt(v___x_6539_, v___x_6544_);
                    if v___x_6552_ == 0 {
                        leanh::lean_dec_ref(v___x_6542_);
                        v___y_6548_ = v___x_6543_;
                        state = 7;
                        continue;
                    } else {
                        v___x_6553_ = lean_nat_dec_le(v___x_6544_, v___x_6544_);
                        if v___x_6553_ == 0 {
                            if v___x_6552_ == 0 {
                                leanh::lean_dec_ref(v___x_6542_);
                                v___y_6548_ = v___x_6543_;
                                state = 7;
                                continue;
                            } else {
                                v___x_6554_ = 0usize;
                                v___x_6555_ = lean_usize_of_nat(v___x_6544_);
                                v___x_6556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_6542_, v___x_6554_, v___x_6555_, v___x_6543_);
                                leanh::lean_dec_ref(v___x_6542_);
                                v___y_6548_ = v___x_6556_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_6557_ = 0usize;
                            v___x_6558_ = lean_usize_of_nat(v___x_6544_);
                            v___x_6559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__2(v___x_6542_, v___x_6557_, v___x_6558_, v___x_6543_);
                            leanh::lean_dec_ref(v___x_6542_);
                            v___y_6548_ = v___x_6559_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6542_);
                    v___x_6560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10_once), _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__10);
                    v_err_6515_ = v___x_6560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_derivedEquations_6516_ = leanh::lean_ctor_get(v_a_6510_, 2);
                leanh::lean_inc_ref(v_derivedEquations_6516_);
                leanh::lean_dec(v_a_6510_);
                v___x_6517_ = leanh::lean_unsigned_to_nat(0);
                v___x_6518_ = lean_array_get_size(v_derivedEquations_6516_);
                v___x_6519_ = lean_nat_dec_lt(v___x_6517_, v___x_6518_);
                if v___x_6519_ == 0 {
                    leanh::lean_dec_ref(v_derivedEquations_6516_);
                    if v_isShared_6513_ == 0 {
                        leanh::lean_ctor_set(v___x_6512_, 0, v_err_6515_);
                        v___x_6521_ = v___x_6512_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_err_6515_);
                        v___x_6521_ = v_reuseFailAlloc_6522_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6523_ = lean_nat_dec_le(v___x_6518_, v___x_6518_);
                    if v___x_6523_ == 0 {
                        if v___x_6519_ == 0 {
                            leanh::lean_dec_ref(v_derivedEquations_6516_);
                            if v_isShared_6513_ == 0 {
                                leanh::lean_ctor_set(v___x_6512_, 0, v_err_6515_);
                                v___x_6525_ = v___x_6512_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_6526_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_err_6515_);
                                v___x_6525_ = v_reuseFailAlloc_6526_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_6527_ = 0usize;
                            v___x_6528_ = lean_usize_of_nat(v___x_6518_);
                            v___x_6529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_6516_, v___x_6527_, v___x_6528_, v_err_6515_);
                            leanh::lean_dec_ref(v_derivedEquations_6516_);
                            if v_isShared_6513_ == 0 {
                                leanh::lean_ctor_set(v___x_6512_, 0, v___x_6529_);
                                v___x_6531_ = v___x_6512_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_6532_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6532_, 0, v___x_6529_);
                                v___x_6531_ = v_reuseFailAlloc_6532_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_6533_ = 0usize;
                        v___x_6534_ = lean_usize_of_nat(v___x_6518_);
                        v___x_6535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality_spec__0(v_derivedEquations_6516_, v___x_6533_, v___x_6534_, v_err_6515_);
                        leanh::lean_dec_ref(v_derivedEquations_6516_);
                        if v_isShared_6513_ == 0 {
                            leanh::lean_ctor_set(v___x_6512_, 0, v___x_6535_);
                            v___x_6537_ = v___x_6512_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6538_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6538_, 0, v___x_6535_);
                            v___x_6537_ = v_reuseFailAlloc_6538_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_6521_;
            }
            4 => {
                return v___x_6525_;
            }
            5 => {
                return v___x_6531_;
            }
            6 => {
                return v___x_6537_;
            }
            7 => {
                v___x_6549_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6549_, 0, v___x_6546_);
                leanh::lean_ctor_set(v___x_6549_, 1, v___y_6548_);
                v___x_6550_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___closed__7,
                );
                v___x_6551_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6551_, 0, v___x_6549_);
                leanh::lean_ctor_set(v___x_6551_, 1, v___x_6550_);
                v_err_6515_ = v___x_6551_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_6565_ == 0 {
                    v___x_6567_ = v___x_6564_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6568_, 0, v_a_6562_);
                    v___x_6567_ = v_reuseFailAlloc_6568_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality___boxed(
    mut v_counterExample_6570_: *mut leanh::LeanObject,
    mut v_a_6571_: *mut leanh::LeanObject,
    mut v_a_6572_: *mut leanh::LeanObject,
    mut v_a_6573_: *mut leanh::LeanObject,
    mut v_a_6574_: *mut leanh::LeanObject,
    mut v_a_6575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6576_ = l_Lean_Meta_Tactic_BVDecide_explainCounterExampleQuality(
        v_counterExample_6570_,
        v_a_6571_,
        v_a_6572_,
        v_a_6573_,
        v_a_6574_,
    );
    leanh::lean_dec(v_a_6574_);
    leanh::lean_dec_ref(v_a_6573_);
    leanh::lean_dec(v_a_6572_);
    leanh::lean_dec_ref(v_a_6571_);
    return v_res_6576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Counterexample(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Enums(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Counterexample(builtin);
}