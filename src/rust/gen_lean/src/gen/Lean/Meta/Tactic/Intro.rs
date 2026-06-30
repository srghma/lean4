// Lean compiler output
// Module: Lean.Meta.Tactic.Intro
// Imports: Lean.Meta.Tactic.Util
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget, lean_array_uset,
    lean_expr_instantiate_rev_range, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Control::Basic::l_instMonadControlTOfPure___redArg;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Meta::Defs::l_Lean_monadNameGeneratorLift___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadLift___lam__0___boxed, l_ReaderT_pure___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadNameGeneratorCoreM, l_Lean_Core_mkFreshUserName,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isExplicit, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_fvarId_x21___boxed, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar,
    l_Lean_Expr_headBeta, l_Lean_Expr_isForall, l_Lean_Expr_isLet, l_Lean_Expr_lam___override,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkFVar, l_Lean_mkFreshFVarId___redArg,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_getUnusedName, l_Lean_LocalContext_mkLetDecl,
    l_Lean_LocalContext_mkLocalDecl,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp,
    l_Lean_MVarId_withContext___redArg, l_Lean_Meta_instMonadMCtxMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_withLCtx_x27___redArg,
    l_Lean_Meta_withNewLocalInstances___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_MVarId_getType, l_Lean_MVarId_getType_x27, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
    l_Lean_Meta_throwTacticEx___redArg, runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MVarId_assign___redArg, l_Lean_instantiateMVars___redArg, l_Lean_instantiateMVarsCore,
};
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 116, 114, 111, 78, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject,3126221519840457472 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2_value: leanh::LeanStringObject<75> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [84, 104, 101, 114, 101, 32, 97, 114, 101, 32, 110, 111, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 98, 105, 110, 100, 101, 114, 115, 32, 111, 114, 32, 96, 108, 101, 116, 96, 32, 98, 105, 110, 100, 105, 110, 103, 115, 32, 105, 110, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 116, 111, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7_value: leanh::LeanClosureObject<3> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0_value:
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
    m_fun: l_Lean_Expr_fvarId_x21___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,16145843736367156323 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10812791644248028522 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [109, 97, 107, 101, 32, 115, 117, 114, 101, 32, 116, 97, 99, 116, 105, 99, 115, 32, 97, 114, 101, 32, 104, 121, 103, 105, 101, 110, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,9078769453211668998 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject,3519807978581637299 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_tactic_hygienic: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value) as *mut leanh::LeanObject,7839396180116328695 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value) as *mut leanh::LeanObject,13286986945483979944 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_introNCore___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_introNCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_introNCore___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_intro1___00__lam__0___closed__0_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            105, 110, 116, 114, 111, 49, 95, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97,
            114, 114, 111, 119, 32, 116, 121, 112, 101, 10, 0,
        ],
    };
static mut l_Lean_MVarId_intro1___00__lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_intro1___00__lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_intro1___00__lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_intro1___00__lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(
    mut v_mvarId_2301_: *mut leanh::LeanObject,
    mut v_type_2302_: *mut leanh::LeanObject,
    mut v_fvars_2303_: *mut leanh::LeanObject,
    mut v_isZero_2304_: u8,
    mut v___x_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
    mut v___y_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533__overap_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_unused_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut v_a_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2347_: u8 = 0;
    let mut v_a_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2351_: u8 = 0;
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut v_a_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_2301_);
                v___x_2311_ = l_Lean_MVarId_getTag(
                    v_mvarId_2301_,
                    v___y_2306_,
                    v___y_2307_,
                    v___y_2308_,
                    v___y_2309_,
                );
                if leanh::lean_obj_tag(v___x_2311_) == 0 {
                    v_a_2312_ = leanh::lean_ctor_get(v___x_2311_, 0);
                    leanh::lean_inc(v_a_2312_);
                    leanh::lean_dec_ref_known(v___x_2311_, 1);
                    v___x_2313_ = l_Lean_Expr_headBeta(v_type_2302_);
                    v___x_2314_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_2313_,
                        v_a_2312_,
                        v___y_2306_,
                        v___y_2307_,
                        v___y_2308_,
                        v___y_2309_,
                    );
                    if leanh::lean_obj_tag(v___x_2314_) == 0 {
                        v_a_2315_ = leanh::lean_ctor_get(v___x_2314_, 0);
                        leanh::lean_inc_n(v_a_2315_, 2);
                        leanh::lean_dec_ref_known(v___x_2314_, 1);
                        v___x_2316_ = 0;
                        v___x_2317_ = 1;
                        v___x_2318_ = l_Lean_Meta_mkLambdaFVars(
                            v_fvars_2303_,
                            v_a_2315_,
                            v___x_2316_,
                            v_isZero_2304_,
                            v___x_2316_,
                            v_isZero_2304_,
                            v___x_2317_,
                            v___y_2306_,
                            v___y_2307_,
                            v___y_2308_,
                            v___y_2309_,
                        );
                        if leanh::lean_obj_tag(v___x_2318_) == 0 {
                            v_a_2319_ = leanh::lean_ctor_get(v___x_2318_, 0);
                            leanh::lean_inc(v_a_2319_);
                            leanh::lean_dec_ref_known(v___x_2318_, 1);
                            v___x_1533__overap_2320_ = l_Lean_MVarId_assign___redArg(
                                v___x_2305_,
                                v_mvarId_2301_,
                                v_a_2319_,
                            );
                            v___x_2321_ = leanh::lean_apply_5(
                                v___x_1533__overap_2320_,
                                v___y_2306_,
                                v___y_2307_,
                                v___y_2308_,
                                v___y_2309_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2321_) == 0 {
                                v_isSharedCheck_2330_ =
                                    (!leanh::lean_is_exclusive(v___x_2321_)) as u8;
                                if v_isSharedCheck_2330_ == 0 {
                                    v_unused_2331_ = leanh::lean_ctor_get(v___x_2321_, 0);
                                    leanh::lean_dec(v_unused_2331_);
                                    v___x_2323_ = v___x_2321_;
                                    v_isShared_2324_ = v_isSharedCheck_2330_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_2321_);
                                    v___x_2323_ = leanh::lean_box(0);
                                    v_isShared_2324_ = v_isSharedCheck_2330_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_2315_);
                                leanh::lean_dec_ref(v_fvars_2303_);
                                v_a_2332_ = leanh::lean_ctor_get(v___x_2321_, 0);
                                v_isSharedCheck_2339_ =
                                    (!leanh::lean_is_exclusive(v___x_2321_)) as u8;
                                if v_isSharedCheck_2339_ == 0 {
                                    v___x_2334_ = v___x_2321_;
                                    v_isShared_2335_ = v_isSharedCheck_2339_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2332_);
                                    leanh::lean_dec(v___x_2321_);
                                    v___x_2334_ = leanh::lean_box(0);
                                    v_isShared_2335_ = v_isSharedCheck_2339_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2315_);
                            leanh::lean_dec(v___y_2309_);
                            leanh::lean_dec_ref(v___y_2308_);
                            leanh::lean_dec(v___y_2307_);
                            leanh::lean_dec_ref(v___y_2306_);
                            leanh::lean_dec_ref(v___x_2305_);
                            leanh::lean_dec_ref(v_fvars_2303_);
                            leanh::lean_dec(v_mvarId_2301_);
                            v_a_2340_ = leanh::lean_ctor_get(v___x_2318_, 0);
                            v_isSharedCheck_2347_ =
                                (!leanh::lean_is_exclusive(v___x_2318_)) as u8;
                            if v_isSharedCheck_2347_ == 0 {
                                v___x_2342_ = v___x_2318_;
                                v_isShared_2343_ = v_isSharedCheck_2347_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2340_);
                                leanh::lean_dec(v___x_2318_);
                                v___x_2342_ = leanh::lean_box(0);
                                v_isShared_2343_ = v_isSharedCheck_2347_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_2309_);
                        leanh::lean_dec_ref(v___y_2308_);
                        leanh::lean_dec(v___y_2307_);
                        leanh::lean_dec_ref(v___y_2306_);
                        leanh::lean_dec_ref(v___x_2305_);
                        leanh::lean_dec_ref(v_fvars_2303_);
                        leanh::lean_dec(v_mvarId_2301_);
                        v_a_2348_ = leanh::lean_ctor_get(v___x_2314_, 0);
                        v_isSharedCheck_2355_ =
                            (!leanh::lean_is_exclusive(v___x_2314_)) as u8;
                        if v_isSharedCheck_2355_ == 0 {
                            v___x_2350_ = v___x_2314_;
                            v_isShared_2351_ = v_isSharedCheck_2355_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2348_);
                            leanh::lean_dec(v___x_2314_);
                            v___x_2350_ = leanh::lean_box(0);
                            v_isShared_2351_ = v_isSharedCheck_2355_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2309_);
                    leanh::lean_dec_ref(v___y_2308_);
                    leanh::lean_dec(v___y_2307_);
                    leanh::lean_dec_ref(v___y_2306_);
                    leanh::lean_dec_ref(v___x_2305_);
                    leanh::lean_dec_ref(v_fvars_2303_);
                    leanh::lean_dec_ref(v_type_2302_);
                    leanh::lean_dec(v_mvarId_2301_);
                    v_a_2356_ = leanh::lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2363_ = (!leanh::lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2358_ = v___x_2311_;
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2356_);
                        leanh::lean_dec(v___x_2311_);
                        v___x_2358_ = leanh::lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2325_ = l_Lean_Expr_mvarId_x21(v_a_2315_);
                leanh::lean_dec(v_a_2315_);
                v___x_2326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2326_, 0, v_fvars_2303_);
                leanh::lean_ctor_set(v___x_2326_, 1, v___x_2325_);
                if v_isShared_2324_ == 0 {
                    leanh::lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2328_;
            }
            3 => {
                if v_isShared_2335_ == 0 {
                    v___x_2337_ = v___x_2334_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
                    v___x_2337_ = v_reuseFailAlloc_2338_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2337_;
            }
            5 => {
                if v_isShared_2343_ == 0 {
                    v___x_2345_ = v___x_2342_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2346_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
                    v___x_2345_ = v_reuseFailAlloc_2346_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2345_;
            }
            7 => {
                if v_isShared_2351_ == 0 {
                    v___x_2353_ = v___x_2350_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
                    v___x_2353_ = v_reuseFailAlloc_2354_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2353_;
            }
            9 => {
                if v_isShared_2359_ == 0 {
                    v___x_2361_ = v___x_2358_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
                    v___x_2361_ = v_reuseFailAlloc_2362_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed(
    mut v_mvarId_2364_: *mut leanh::LeanObject,
    mut v_type_2365_: *mut leanh::LeanObject,
    mut v_fvars_2366_: *mut leanh::LeanObject,
    mut v_isZero_2367_: *mut leanh::LeanObject,
    mut v___x_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isZero_boxed_2374_: u8 = 0;
    let mut v_res_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_2374_ = (leanh::lean_unbox(v_isZero_2367_) as u8);
    v_res_2375_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(
        v_mvarId_2364_,
        v_type_2365_,
        v_fvars_2366_,
        v_isZero_boxed_2374_,
        v___x_2368_,
        v___y_2369_,
        v___y_2370_,
        v___y_2371_,
        v___y_2372_,
    );
    return v_res_2375_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2380_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2;
    v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
    return v___x_2381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3);
    v___x_2383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0);
    v___x_2386_ = l_StateRefT_x27_instMonad___redArg(v___x_2385_);
    return v___x_2386_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_Core_instMonadNameGeneratorCoreM;
    v___x_2393_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7;
    v___x_2394_ = l_Lean_monadNameGeneratorLift___redArg(v___x_2393_, v___x_2392_);
    return v___x_2394_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8);
    v___f_2397_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6;
    v___x_2398_ = l_Lean_monadNameGeneratorLift___redArg(v___f_2397_, v___x_2396_);
    return v___x_2398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed(
    mut v___x_2399_: *mut leanh::LeanObject,
    mut v___x_2400_: *mut leanh::LeanObject,
    mut v_type_2401_: *mut leanh::LeanObject,
    mut v_mvarId_2402_: *mut leanh::LeanObject,
    mut v_n_2403_: *mut leanh::LeanObject,
    mut v_mkName_2404_: *mut leanh::LeanObject,
    mut v_lctx_2405_: *mut leanh::LeanObject,
    mut v_fvars_2406_: *mut leanh::LeanObject,
    mut v___x_2407_: *mut leanh::LeanObject,
    mut v_s_2408_: *mut leanh::LeanObject,
    mut v___y_2409_: *mut leanh::LeanObject,
    mut v___y_2410_: *mut leanh::LeanObject,
    mut v___y_2411_: *mut leanh::LeanObject,
    mut v___y_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2414_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(
        v___x_2399_,
        v___x_2400_,
        v_type_2401_,
        v_mvarId_2402_,
        v_n_2403_,
        v_mkName_2404_,
        v_lctx_2405_,
        v_fvars_2406_,
        v___x_2407_,
        v_s_2408_,
        v___y_2409_,
        v___y_2410_,
        v___y_2411_,
        v___y_2412_,
    );
    leanh::lean_dec(v_n_2403_);
    return v_res_2414_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(
    mut v_mvarId_2415_: *mut leanh::LeanObject,
    mut v_mkName_2416_: *mut leanh::LeanObject,
    mut v_i_2417_: *mut leanh::LeanObject,
    mut v_lctx_2418_: *mut leanh::LeanObject,
    mut v_fvars_2419_: *mut leanh::LeanObject,
    mut v_j_2420_: *mut leanh::LeanObject,
    mut v_s_2421_: *mut leanh::LeanObject,
    mut v_type_2422_: *mut leanh::LeanObject,
    mut v_a_2423_: *mut leanh::LeanObject,
    mut v_a_2424_: *mut leanh::LeanObject,
    mut v_a_2425_: *mut leanh::LeanObject,
    mut v_a_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v_toFunctor_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___f_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2487_: u8 = 0;
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284__overap_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314__overap_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_a_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_binderName_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2538_: u8 = 0;
    let mut v___x_1363__overap_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_a_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437__overap_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v_unused_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_unused_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
                v_toApplicative_2429_ = leanh::lean_ctor_get(v___x_2428_, 0);
                v_toFunctor_2430_ = leanh::lean_ctor_get(v_toApplicative_2429_, 0);
                v_toSeq_2431_ = leanh::lean_ctor_get(v_toApplicative_2429_, 2);
                v_toSeqLeft_2432_ = leanh::lean_ctor_get(v_toApplicative_2429_, 3);
                v_toSeqRight_2433_ = leanh::lean_ctor_get(v_toApplicative_2429_, 4);
                v___f_2434_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2;
                v___f_2435_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2430_, 2);
                v___f_2436_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2436_, 0, v_toFunctor_2430_);
                v___f_2437_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2437_, 0, v_toFunctor_2430_);
                v___x_2438_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2438_, 0, v___f_2436_);
                leanh::lean_ctor_set(v___x_2438_, 1, v___f_2437_);
                leanh::lean_inc(v_toSeqRight_2433_);
                v___f_2439_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2439_, 0, v_toSeqRight_2433_);
                leanh::lean_inc(v_toSeqLeft_2432_);
                v___f_2440_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2440_, 0, v_toSeqLeft_2432_);
                leanh::lean_inc(v_toSeq_2431_);
                v___f_2441_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2441_, 0, v_toSeq_2431_);
                v___x_2442_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2442_, 0, v___x_2438_);
                leanh::lean_ctor_set(v___x_2442_, 1, v___f_2434_);
                leanh::lean_ctor_set(v___x_2442_, 2, v___f_2441_);
                leanh::lean_ctor_set(v___x_2442_, 3, v___f_2440_);
                leanh::lean_ctor_set(v___x_2442_, 4, v___f_2439_);
                v___x_2443_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
                leanh::lean_ctor_set(v___x_2443_, 1, v___f_2435_);
                v___x_2444_ = l_StateRefT_x27_instMonad___redArg(v___x_2443_);
                v___x_2445_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2445_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2445_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2445_, 2, v___x_2444_);
                v___x_2446_ = l_instMonadControlTOfPure___redArg(v___x_2445_);
                v_toApplicative_2447_ = leanh::lean_ctor_get(v___x_2428_, 0);
                v_toFunctor_2448_ = leanh::lean_ctor_get(v_toApplicative_2447_, 0);
                v_toSeq_2449_ = leanh::lean_ctor_get(v_toApplicative_2447_, 2);
                v_toSeqLeft_2450_ = leanh::lean_ctor_get(v_toApplicative_2447_, 3);
                v_toSeqRight_2451_ = leanh::lean_ctor_get(v_toApplicative_2447_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2448_, 2);
                v___f_2452_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2452_, 0, v_toFunctor_2448_);
                v___f_2453_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2453_, 0, v_toFunctor_2448_);
                v___x_2454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2454_, 0, v___f_2452_);
                leanh::lean_ctor_set(v___x_2454_, 1, v___f_2453_);
                leanh::lean_inc(v_toSeqRight_2451_);
                v___f_2455_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2455_, 0, v_toSeqRight_2451_);
                leanh::lean_inc(v_toSeqLeft_2450_);
                v___f_2456_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2456_, 0, v_toSeqLeft_2450_);
                leanh::lean_inc(v_toSeq_2449_);
                v___f_2457_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2457_, 0, v_toSeq_2449_);
                v___x_2458_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2458_, 0, v___x_2454_);
                leanh::lean_ctor_set(v___x_2458_, 1, v___f_2434_);
                leanh::lean_ctor_set(v___x_2458_, 2, v___f_2457_);
                leanh::lean_ctor_set(v___x_2458_, 3, v___f_2456_);
                leanh::lean_ctor_set(v___x_2458_, 4, v___f_2455_);
                v___x_2459_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2459_, 0, v___x_2458_);
                leanh::lean_ctor_set(v___x_2459_, 1, v___f_2435_);
                v___x_2460_ = l_StateRefT_x27_instMonad___redArg(v___x_2459_);
                v_toApplicative_2461_ = leanh::lean_ctor_get(v___x_2460_, 0);
                v_isSharedCheck_2582_ = (!leanh::lean_is_exclusive(v___x_2460_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v_unused_2583_ = leanh::lean_ctor_get(v___x_2460_, 1);
                    leanh::lean_dec(v_unused_2583_);
                    v___x_2463_ = v___x_2460_;
                    v_isShared_2464_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2461_);
                    leanh::lean_dec(v___x_2460_);
                    v___x_2463_ = leanh::lean_box(0);
                    v_isShared_2464_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2465_ = leanh::lean_ctor_get(v_toApplicative_2461_, 0);
                v_toSeq_2466_ = leanh::lean_ctor_get(v_toApplicative_2461_, 2);
                v_toSeqLeft_2467_ = leanh::lean_ctor_get(v_toApplicative_2461_, 3);
                v_toSeqRight_2468_ = leanh::lean_ctor_get(v_toApplicative_2461_, 4);
                v_isSharedCheck_2580_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2461_)) as u8;
                if v_isSharedCheck_2580_ == 0 {
                    v_unused_2581_ = leanh::lean_ctor_get(v_toApplicative_2461_, 1);
                    leanh::lean_dec(v_unused_2581_);
                    v___x_2470_ = v_toApplicative_2461_;
                    v_isShared_2471_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2468_);
                    leanh::lean_inc(v_toSeqLeft_2467_);
                    leanh::lean_inc(v_toSeq_2466_);
                    leanh::lean_inc(v_toFunctor_2465_);
                    leanh::lean_dec(v_toApplicative_2461_);
                    v___x_2470_ = leanh::lean_box(0);
                    v_isShared_2471_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2472_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4;
                v___f_2473_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_2465_);
                v___f_2474_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2474_, 0, v_toFunctor_2465_);
                v___f_2475_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2475_, 0, v_toFunctor_2465_);
                v___x_2476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2476_, 0, v___f_2474_);
                leanh::lean_ctor_set(v___x_2476_, 1, v___f_2475_);
                v___f_2477_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2477_, 0, v_toSeqRight_2468_);
                v___f_2478_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2478_, 0, v_toSeqLeft_2467_);
                v___f_2479_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2479_, 0, v_toSeq_2466_);
                if v_isShared_2471_ == 0 {
                    leanh::lean_ctor_set(v___x_2470_, 4, v___f_2477_);
                    leanh::lean_ctor_set(v___x_2470_, 3, v___f_2478_);
                    leanh::lean_ctor_set(v___x_2470_, 2, v___f_2479_);
                    leanh::lean_ctor_set(v___x_2470_, 1, v___f_2472_);
                    leanh::lean_ctor_set(v___x_2470_, 0, v___x_2476_);
                    v___x_2481_ = v___x_2470_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___f_2472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 2, v___f_2479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 3, v___f_2478_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 4, v___f_2477_);
                    v___x_2481_ = v_reuseFailAlloc_2579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2464_ == 0 {
                    leanh::lean_ctor_set(v___x_2463_, 1, v___f_2473_);
                    leanh::lean_ctor_set(v___x_2463_, 0, v___x_2481_);
                    v___x_2483_ = v___x_2463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___f_2473_);
                    v___x_2483_ = v_reuseFailAlloc_2578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2484_ = l_Lean_Meta_instMonadMCtxMetaM;
                v___x_2485_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9);
                v_zero_2486_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2487_ = lean_nat_dec_eq(v_i_2417_, v_zero_2486_);
                if v_isZero_2487_ == 1 {
                    leanh::lean_dec(v_s_2421_);
                    leanh::lean_dec(v_i_2417_);
                    leanh::lean_dec_ref(v_mkName_2416_);
                    v___x_2488_ = lean_array_get_size(v_fvars_2419_);
                    v_type_2489_ = lean_expr_instantiate_rev_range(
                        v_type_2422_,
                        v_j_2420_,
                        v___x_2488_,
                        v_fvars_2419_,
                    );
                    leanh::lean_dec_ref(v_type_2422_);
                    v___x_2490_ = leanh::lean_box((v_isZero_2487_) as usize);
                    leanh::lean_inc_ref(v_fvars_2419_);
                    v___f_2491_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                    leanh::lean_closure_set(v___f_2491_, 0, v_mvarId_2415_);
                    leanh::lean_closure_set(v___f_2491_, 1, v_type_2489_);
                    leanh::lean_closure_set(v___f_2491_, 2, v_fvars_2419_);
                    leanh::lean_closure_set(v___f_2491_, 3, v___x_2490_);
                    leanh::lean_closure_set(v___f_2491_, 4, v___x_2484_);
                    leanh::lean_inc_ref(v___x_2483_);
                    leanh::lean_inc_ref(v___x_2446_);
                    v___x_2492_ = l_Lean_Meta_withNewLocalInstances___redArg(
                        v___x_2446_,
                        v___x_2483_,
                        v_fvars_2419_,
                        v_j_2420_,
                        v___f_2491_,
                    );
                    v___x_1284__overap_2493_ = l_Lean_Meta_withLCtx_x27___redArg(
                        v___x_2446_,
                        v___x_2483_,
                        v_lctx_2418_,
                        v___x_2492_,
                    );
                    leanh::lean_inc(v_a_2426_);
                    leanh::lean_inc_ref(v_a_2425_);
                    leanh::lean_inc(v_a_2424_);
                    leanh::lean_inc_ref(v_a_2423_);
                    v___x_2494_ = leanh::lean_apply_5(
                        v___x_1284__overap_2493_,
                        v_a_2423_,
                        v_a_2424_,
                        v_a_2425_,
                        v_a_2426_,
                        leanh::lean_box(0),
                    );
                    return v___x_2494_;
                } else {
                    v_one_2495_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2496_ = lean_nat_sub(v_i_2417_, v_one_2495_);
                    leanh::lean_dec(v_i_2417_);
                    match leanh::lean_obj_tag(v_type_2422_) {
                        8 => {
                            leanh::lean_dec_ref(v___x_2446_);
                            v_declName_2497_ = leanh::lean_ctor_get(v_type_2422_, 0);
                            leanh::lean_inc(v_declName_2497_);
                            v_type_2498_ = leanh::lean_ctor_get(v_type_2422_, 1);
                            leanh::lean_inc_ref(v_type_2498_);
                            v_value_2499_ = leanh::lean_ctor_get(v_type_2422_, 2);
                            leanh::lean_inc_ref(v_value_2499_);
                            v_body_2500_ = leanh::lean_ctor_get(v_type_2422_, 3);
                            leanh::lean_inc_ref(v_body_2500_);
                            leanh::lean_dec_ref_known(v_type_2422_, 4);
                            v___x_1314__overap_2501_ =
                                l_Lean_mkFreshFVarId___redArg(v___x_2483_, v___x_2485_);
                            leanh::lean_inc(v_a_2426_);
                            leanh::lean_inc_ref(v_a_2425_);
                            leanh::lean_inc(v_a_2424_);
                            leanh::lean_inc_ref(v_a_2423_);
                            v___x_2502_ = leanh::lean_apply_5(
                                v___x_1314__overap_2501_,
                                v_a_2423_,
                                v_a_2424_,
                                v_a_2425_,
                                v_a_2426_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2502_) == 0 {
                                v_a_2503_ = leanh::lean_ctor_get(v___x_2502_, 0);
                                leanh::lean_inc(v_a_2503_);
                                leanh::lean_dec_ref_known(v___x_2502_, 1);
                                v___x_2504_ = 1;
                                v___x_2505_ = leanh::lean_box((v___x_2504_) as usize);
                                leanh::lean_inc_ref(v_mkName_2416_);
                                leanh::lean_inc(v_a_2426_);
                                leanh::lean_inc_ref(v_a_2425_);
                                leanh::lean_inc(v_a_2424_);
                                leanh::lean_inc_ref(v_a_2423_);
                                leanh::lean_inc_ref(v_lctx_2418_);
                                v___x_2506_ = leanh::lean_apply_9(
                                    v_mkName_2416_,
                                    v_lctx_2418_,
                                    v_declName_2497_,
                                    v___x_2505_,
                                    v_s_2421_,
                                    v_a_2423_,
                                    v_a_2424_,
                                    v_a_2425_,
                                    v_a_2426_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_2506_) == 0 {
                                    v_a_2507_ = leanh::lean_ctor_get(v___x_2506_, 0);
                                    leanh::lean_inc(v_a_2507_);
                                    leanh::lean_dec_ref_known(v___x_2506_, 1);
                                    v_fst_2508_ = leanh::lean_ctor_get(v_a_2507_, 0);
                                    leanh::lean_inc(v_fst_2508_);
                                    v_snd_2509_ = leanh::lean_ctor_get(v_a_2507_, 1);
                                    leanh::lean_inc(v_snd_2509_);
                                    leanh::lean_dec(v_a_2507_);
                                    v___x_2510_ = lean_array_get_size(v_fvars_2419_);
                                    v_type_2511_ = lean_expr_instantiate_rev_range(
                                        v_type_2498_,
                                        v_j_2420_,
                                        v___x_2510_,
                                        v_fvars_2419_,
                                    );
                                    leanh::lean_dec_ref(v_type_2498_);
                                    v_type_2512_ = l_Lean_Expr_headBeta(v_type_2511_);
                                    v_val_2513_ = lean_expr_instantiate_rev_range(
                                        v_value_2499_,
                                        v_j_2420_,
                                        v___x_2510_,
                                        v_fvars_2419_,
                                    );
                                    leanh::lean_dec_ref(v_value_2499_);
                                    v___x_2514_ = 0;
                                    leanh::lean_inc(v_a_2503_);
                                    v___x_2515_ = l_Lean_LocalContext_mkLetDecl(
                                        v_lctx_2418_,
                                        v_a_2503_,
                                        v_fst_2508_,
                                        v_type_2512_,
                                        v_val_2513_,
                                        v_isZero_2487_,
                                        v___x_2514_,
                                    );
                                    v___x_2516_ = l_Lean_mkFVar(v_a_2503_);
                                    v___x_2517_ = lean_array_push(v_fvars_2419_, v___x_2516_);
                                    v_i_2417_ = v_n_2496_;
                                    v_lctx_2418_ = v___x_2515_;
                                    v_fvars_2419_ = v___x_2517_;
                                    v_s_2421_ = v_snd_2509_;
                                    v_type_2422_ = v_body_2500_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_2503_);
                                    leanh::lean_dec_ref(v_body_2500_);
                                    leanh::lean_dec_ref(v_value_2499_);
                                    leanh::lean_dec_ref(v_type_2498_);
                                    leanh::lean_dec(v_n_2496_);
                                    leanh::lean_dec(v_j_2420_);
                                    leanh::lean_dec_ref(v_fvars_2419_);
                                    leanh::lean_dec_ref(v_lctx_2418_);
                                    leanh::lean_dec_ref(v_mkName_2416_);
                                    leanh::lean_dec(v_mvarId_2415_);
                                    v_a_2519_ = leanh::lean_ctor_get(v___x_2506_, 0);
                                    v_isSharedCheck_2526_ =
                                        (!leanh::lean_is_exclusive(v___x_2506_)) as u8;
                                    if v_isSharedCheck_2526_ == 0 {
                                        v___x_2521_ = v___x_2506_;
                                        v_isShared_2522_ = v_isSharedCheck_2526_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2519_);
                                        leanh::lean_dec(v___x_2506_);
                                        v___x_2521_ = leanh::lean_box(0);
                                        v_isShared_2522_ = v_isSharedCheck_2526_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_2500_);
                                leanh::lean_dec_ref(v_value_2499_);
                                leanh::lean_dec_ref(v_type_2498_);
                                leanh::lean_dec(v_declName_2497_);
                                leanh::lean_dec(v_n_2496_);
                                leanh::lean_dec(v_s_2421_);
                                leanh::lean_dec(v_j_2420_);
                                leanh::lean_dec_ref(v_fvars_2419_);
                                leanh::lean_dec_ref(v_lctx_2418_);
                                leanh::lean_dec_ref(v_mkName_2416_);
                                leanh::lean_dec(v_mvarId_2415_);
                                v_a_2527_ = leanh::lean_ctor_get(v___x_2502_, 0);
                                v_isSharedCheck_2534_ =
                                    (!leanh::lean_is_exclusive(v___x_2502_)) as u8;
                                if v_isSharedCheck_2534_ == 0 {
                                    v___x_2529_ = v___x_2502_;
                                    v_isShared_2530_ = v_isSharedCheck_2534_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2527_);
                                    leanh::lean_dec(v___x_2502_);
                                    v___x_2529_ = leanh::lean_box(0);
                                    v_isShared_2530_ = v_isSharedCheck_2534_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        7 => {
                            leanh::lean_dec_ref(v___x_2446_);
                            v_binderName_2535_ = leanh::lean_ctor_get(v_type_2422_, 0);
                            leanh::lean_inc(v_binderName_2535_);
                            v_binderType_2536_ = leanh::lean_ctor_get(v_type_2422_, 1);
                            leanh::lean_inc_ref(v_binderType_2536_);
                            v_body_2537_ = leanh::lean_ctor_get(v_type_2422_, 2);
                            leanh::lean_inc_ref(v_body_2537_);
                            v_binderInfo_2538_ = leanh::lean_ctor_get_uint8(
                                v_type_2422_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_type_2422_, 3);
                            v___x_1363__overap_2539_ =
                                l_Lean_mkFreshFVarId___redArg(v___x_2483_, v___x_2485_);
                            leanh::lean_inc(v_a_2426_);
                            leanh::lean_inc_ref(v_a_2425_);
                            leanh::lean_inc(v_a_2424_);
                            leanh::lean_inc_ref(v_a_2423_);
                            v___x_2540_ = leanh::lean_apply_5(
                                v___x_1363__overap_2539_,
                                v_a_2423_,
                                v_a_2424_,
                                v_a_2425_,
                                v_a_2426_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2540_) == 0 {
                                v_a_2541_ = leanh::lean_ctor_get(v___x_2540_, 0);
                                leanh::lean_inc(v_a_2541_);
                                leanh::lean_dec_ref_known(v___x_2540_, 1);
                                v___x_2542_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2538_);
                                v___x_2543_ = leanh::lean_box((v___x_2542_) as usize);
                                leanh::lean_inc_ref(v_mkName_2416_);
                                leanh::lean_inc(v_a_2426_);
                                leanh::lean_inc_ref(v_a_2425_);
                                leanh::lean_inc(v_a_2424_);
                                leanh::lean_inc_ref(v_a_2423_);
                                leanh::lean_inc_ref(v_lctx_2418_);
                                v___x_2544_ = leanh::lean_apply_9(
                                    v_mkName_2416_,
                                    v_lctx_2418_,
                                    v_binderName_2535_,
                                    v___x_2543_,
                                    v_s_2421_,
                                    v_a_2423_,
                                    v_a_2424_,
                                    v_a_2425_,
                                    v_a_2426_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_2544_) == 0 {
                                    v_a_2545_ = leanh::lean_ctor_get(v___x_2544_, 0);
                                    leanh::lean_inc(v_a_2545_);
                                    leanh::lean_dec_ref_known(v___x_2544_, 1);
                                    v_fst_2546_ = leanh::lean_ctor_get(v_a_2545_, 0);
                                    leanh::lean_inc(v_fst_2546_);
                                    v_snd_2547_ = leanh::lean_ctor_get(v_a_2545_, 1);
                                    leanh::lean_inc(v_snd_2547_);
                                    leanh::lean_dec(v_a_2545_);
                                    v___x_2548_ = lean_array_get_size(v_fvars_2419_);
                                    v_type_2549_ = lean_expr_instantiate_rev_range(
                                        v_binderType_2536_,
                                        v_j_2420_,
                                        v___x_2548_,
                                        v_fvars_2419_,
                                    );
                                    leanh::lean_dec_ref(v_binderType_2536_);
                                    v_type_2550_ = l_Lean_Expr_headBeta(v_type_2549_);
                                    v___x_2551_ = 0;
                                    leanh::lean_inc(v_a_2541_);
                                    v___x_2552_ = l_Lean_LocalContext_mkLocalDecl(
                                        v_lctx_2418_,
                                        v_a_2541_,
                                        v_fst_2546_,
                                        v_type_2550_,
                                        v_binderInfo_2538_,
                                        v___x_2551_,
                                    );
                                    v___x_2553_ = l_Lean_mkFVar(v_a_2541_);
                                    v___x_2554_ = lean_array_push(v_fvars_2419_, v___x_2553_);
                                    v_i_2417_ = v_n_2496_;
                                    v_lctx_2418_ = v___x_2552_;
                                    v_fvars_2419_ = v___x_2554_;
                                    v_s_2421_ = v_snd_2547_;
                                    v_type_2422_ = v_body_2537_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_2541_);
                                    leanh::lean_dec_ref(v_body_2537_);
                                    leanh::lean_dec_ref(v_binderType_2536_);
                                    leanh::lean_dec(v_n_2496_);
                                    leanh::lean_dec(v_j_2420_);
                                    leanh::lean_dec_ref(v_fvars_2419_);
                                    leanh::lean_dec_ref(v_lctx_2418_);
                                    leanh::lean_dec_ref(v_mkName_2416_);
                                    leanh::lean_dec(v_mvarId_2415_);
                                    v_a_2556_ = leanh::lean_ctor_get(v___x_2544_, 0);
                                    v_isSharedCheck_2563_ =
                                        (!leanh::lean_is_exclusive(v___x_2544_)) as u8;
                                    if v_isSharedCheck_2563_ == 0 {
                                        v___x_2558_ = v___x_2544_;
                                        v_isShared_2559_ = v_isSharedCheck_2563_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2556_);
                                        leanh::lean_dec(v___x_2544_);
                                        v___x_2558_ = leanh::lean_box(0);
                                        v_isShared_2559_ = v_isSharedCheck_2563_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_2537_);
                                leanh::lean_dec_ref(v_binderType_2536_);
                                leanh::lean_dec(v_binderName_2535_);
                                leanh::lean_dec(v_n_2496_);
                                leanh::lean_dec(v_s_2421_);
                                leanh::lean_dec(v_j_2420_);
                                leanh::lean_dec_ref(v_fvars_2419_);
                                leanh::lean_dec_ref(v_lctx_2418_);
                                leanh::lean_dec_ref(v_mkName_2416_);
                                leanh::lean_dec(v_mvarId_2415_);
                                v_a_2564_ = leanh::lean_ctor_get(v___x_2540_, 0);
                                v_isSharedCheck_2571_ =
                                    (!leanh::lean_is_exclusive(v___x_2540_)) as u8;
                                if v_isSharedCheck_2571_ == 0 {
                                    v___x_2566_ = v___x_2540_;
                                    v_isShared_2567_ = v_isSharedCheck_2571_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2564_);
                                    leanh::lean_dec(v___x_2540_);
                                    v___x_2566_ = leanh::lean_box(0);
                                    v_isShared_2567_ = v_isSharedCheck_2571_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v___x_2572_ = lean_array_get_size(v_fvars_2419_);
                            v_type_2573_ = lean_expr_instantiate_rev_range(
                                v_type_2422_,
                                v_j_2420_,
                                v___x_2572_,
                                v_fvars_2419_,
                            );
                            leanh::lean_dec_ref(v_type_2422_);
                            leanh::lean_inc_ref(v_fvars_2419_);
                            leanh::lean_inc_ref(v_lctx_2418_);
                            leanh::lean_inc_ref_n(v___x_2483_, 2);
                            v___f_2574_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed as *mut core::ffi::c_void, 15, 10);
                            leanh::lean_closure_set(v___f_2574_, 0, v___x_2483_);
                            leanh::lean_closure_set(v___f_2574_, 1, v___x_2484_);
                            leanh::lean_closure_set(v___f_2574_, 2, v_type_2573_);
                            leanh::lean_closure_set(v___f_2574_, 3, v_mvarId_2415_);
                            leanh::lean_closure_set(v___f_2574_, 4, v_n_2496_);
                            leanh::lean_closure_set(v___f_2574_, 5, v_mkName_2416_);
                            leanh::lean_closure_set(v___f_2574_, 6, v_lctx_2418_);
                            leanh::lean_closure_set(v___f_2574_, 7, v_fvars_2419_);
                            leanh::lean_closure_set(v___f_2574_, 8, v___x_2572_);
                            leanh::lean_closure_set(v___f_2574_, 9, v_s_2421_);
                            leanh::lean_inc_ref(v___x_2446_);
                            v___x_2575_ = l_Lean_Meta_withNewLocalInstances___redArg(
                                v___x_2446_,
                                v___x_2483_,
                                v_fvars_2419_,
                                v_j_2420_,
                                v___f_2574_,
                            );
                            v___x_1437__overap_2576_ = l_Lean_Meta_withLCtx_x27___redArg(
                                v___x_2446_,
                                v___x_2483_,
                                v_lctx_2418_,
                                v___x_2575_,
                            );
                            leanh::lean_inc(v_a_2426_);
                            leanh::lean_inc_ref(v_a_2425_);
                            leanh::lean_inc(v_a_2424_);
                            leanh::lean_inc_ref(v_a_2423_);
                            v___x_2577_ = leanh::lean_apply_5(
                                v___x_1437__overap_2576_,
                                v_a_2423_,
                                v_a_2424_,
                                v_a_2425_,
                                v_a_2426_,
                                leanh::lean_box(0),
                            );
                            return v___x_2577_;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_2522_ == 0 {
                    v___x_2524_ = v___x_2521_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
                    v___x_2524_ = v_reuseFailAlloc_2525_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2524_;
            }
            7 => {
                if v_isShared_2530_ == 0 {
                    v___x_2532_ = v___x_2529_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2532_;
            }
            9 => {
                if v_isShared_2559_ == 0 {
                    v___x_2561_ = v___x_2558_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
                    v___x_2561_ = v_reuseFailAlloc_2562_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2561_;
            }
            11 => {
                if v_isShared_2567_ == 0 {
                    v___x_2569_ = v___x_2566_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
                    v___x_2569_ = v_reuseFailAlloc_2570_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1(
    mut v___x_2584_: *mut leanh::LeanObject,
    mut v___x_2585_: *mut leanh::LeanObject,
    mut v_type_2586_: *mut leanh::LeanObject,
    mut v_mvarId_2587_: *mut leanh::LeanObject,
    mut v_n_2588_: *mut leanh::LeanObject,
    mut v_mkName_2589_: *mut leanh::LeanObject,
    mut v_lctx_2590_: *mut leanh::LeanObject,
    mut v_fvars_2591_: *mut leanh::LeanObject,
    mut v___x_2592_: *mut leanh::LeanObject,
    mut v_s_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
    mut v___y_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1560__overap_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: u8 = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: u8 = 0;
    let mut v___x_2626_: u8 = 0;
    let mut v_a_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1560__overap_2599_ =
                    l_Lean_instantiateMVars___redArg(v___x_2584_, v___x_2585_, v_type_2586_);
                leanh::lean_inc(v___y_2597_);
                leanh::lean_inc_ref(v___y_2596_);
                leanh::lean_inc(v___y_2595_);
                leanh::lean_inc_ref(v___y_2594_);
                v___x_2600_ = leanh::lean_apply_5(
                    v___x_1560__overap_2599_,
                    v___y_2594_,
                    v___y_2595_,
                    v___y_2596_,
                    v___y_2597_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2600_) == 0 {
                    v_a_2601_ = leanh::lean_ctor_get(v___x_2600_, 0);
                    leanh::lean_inc(v_a_2601_);
                    leanh::lean_dec_ref_known(v___x_2600_, 1);
                    v___x_2602_ = l_Lean_Expr_cleanupAnnotations(v_a_2601_);
                    v___x_2625_ = l_Lean_Expr_isForall(v___x_2602_);
                    if v___x_2625_ == 0 {
                        v___x_2626_ = l_Lean_Expr_isLet(v___x_2602_);
                        v___y_2604_ = v___x_2626_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2604_ = v___x_2625_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2597_);
                    leanh::lean_dec_ref(v___y_2596_);
                    leanh::lean_dec(v___y_2595_);
                    leanh::lean_dec_ref(v___y_2594_);
                    leanh::lean_dec(v_s_2593_);
                    leanh::lean_dec(v___x_2592_);
                    leanh::lean_dec_ref(v_fvars_2591_);
                    leanh::lean_dec_ref(v_lctx_2590_);
                    leanh::lean_dec_ref(v_mkName_2589_);
                    leanh::lean_dec(v_mvarId_2587_);
                    v_a_2627_ = leanh::lean_ctor_get(v___x_2600_, 0);
                    v_isSharedCheck_2634_ = (!leanh::lean_is_exclusive(v___x_2600_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2629_ = v___x_2600_;
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2627_);
                        leanh::lean_dec(v___x_2600_);
                        v___x_2629_ = leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2604_ == 0 {
                    leanh::lean_inc(v___y_2597_);
                    leanh::lean_inc_ref(v___y_2596_);
                    leanh::lean_inc(v___y_2595_);
                    leanh::lean_inc_ref(v___y_2594_);
                    v___x_2605_ = lean_whnf(
                        v___x_2602_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if leanh::lean_obj_tag(v___x_2605_) == 0 {
                        v_a_2606_ = leanh::lean_ctor_get(v___x_2605_, 0);
                        leanh::lean_inc(v_a_2606_);
                        leanh::lean_dec_ref_known(v___x_2605_, 1);
                        v___x_2607_ = l_Lean_Expr_isForall(v_a_2606_);
                        if v___x_2607_ == 0 {
                            leanh::lean_dec(v_a_2606_);
                            leanh::lean_dec(v_s_2593_);
                            leanh::lean_dec(v___x_2592_);
                            leanh::lean_dec_ref(v_fvars_2591_);
                            leanh::lean_dec_ref(v_lctx_2590_);
                            leanh::lean_dec_ref(v_mkName_2589_);
                            v___x_2608_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                            v___x_2609_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
                            v___x_2610_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_2608_,
                                v_mvarId_2587_,
                                v___x_2609_,
                                v___y_2594_,
                                v___y_2595_,
                                v___y_2596_,
                                v___y_2597_,
                            );
                            leanh::lean_dec(v___y_2597_);
                            leanh::lean_dec_ref(v___y_2596_);
                            leanh::lean_dec(v___y_2595_);
                            leanh::lean_dec_ref(v___y_2594_);
                            return v___x_2610_;
                        } else {
                            v___x_2611_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2612_ = lean_nat_add(v_n_2588_, v___x_2611_);
                            v___x_2613_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_2587_, v_mkName_2589_, v___x_2612_, v_lctx_2590_, v_fvars_2591_, v___x_2592_, v_s_2593_, v_a_2606_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
                            leanh::lean_dec(v___y_2597_);
                            leanh::lean_dec_ref(v___y_2596_);
                            leanh::lean_dec(v___y_2595_);
                            leanh::lean_dec_ref(v___y_2594_);
                            return v___x_2613_;
                        }
                    } else {
                        leanh::lean_dec(v___y_2597_);
                        leanh::lean_dec_ref(v___y_2596_);
                        leanh::lean_dec(v___y_2595_);
                        leanh::lean_dec_ref(v___y_2594_);
                        leanh::lean_dec(v_s_2593_);
                        leanh::lean_dec(v___x_2592_);
                        leanh::lean_dec_ref(v_fvars_2591_);
                        leanh::lean_dec_ref(v_lctx_2590_);
                        leanh::lean_dec_ref(v_mkName_2589_);
                        leanh::lean_dec(v_mvarId_2587_);
                        v_a_2614_ = leanh::lean_ctor_get(v___x_2605_, 0);
                        v_isSharedCheck_2621_ =
                            (!leanh::lean_is_exclusive(v___x_2605_)) as u8;
                        if v_isSharedCheck_2621_ == 0 {
                            v___x_2616_ = v___x_2605_;
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2614_);
                            leanh::lean_dec(v___x_2605_);
                            v___x_2616_ = leanh::lean_box(0);
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2622_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2623_ = lean_nat_add(v_n_2588_, v___x_2622_);
                    v___x_2624_ =
                        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(
                            v_mvarId_2587_,
                            v_mkName_2589_,
                            v___x_2623_,
                            v_lctx_2590_,
                            v_fvars_2591_,
                            v___x_2592_,
                            v_s_2593_,
                            v___x_2602_,
                            v___y_2594_,
                            v___y_2595_,
                            v___y_2596_,
                            v___y_2597_,
                        );
                    leanh::lean_dec(v___y_2597_);
                    leanh::lean_dec_ref(v___y_2596_);
                    leanh::lean_dec(v___y_2595_);
                    leanh::lean_dec_ref(v___y_2594_);
                    return v___x_2624_;
                }
            }
            2 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
                    v___x_2619_ = v_reuseFailAlloc_2620_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2619_;
            }
            4 => {
                if v_isShared_2630_ == 0 {
                    v___x_2632_ = v___x_2629_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___boxed(
    mut v_mvarId_2635_: *mut leanh::LeanObject,
    mut v_mkName_2636_: *mut leanh::LeanObject,
    mut v_i_2637_: *mut leanh::LeanObject,
    mut v_lctx_2638_: *mut leanh::LeanObject,
    mut v_fvars_2639_: *mut leanh::LeanObject,
    mut v_j_2640_: *mut leanh::LeanObject,
    mut v_s_2641_: *mut leanh::LeanObject,
    mut v_type_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(
        v_mvarId_2635_,
        v_mkName_2636_,
        v_i_2637_,
        v_lctx_2638_,
        v_fvars_2639_,
        v_j_2640_,
        v_s_2641_,
        v_type_2642_,
        v_a_2643_,
        v_a_2644_,
        v_a_2645_,
        v_a_2646_,
    );
    leanh::lean_dec(v_a_2646_);
    leanh::lean_dec_ref(v_a_2645_);
    leanh::lean_dec(v_a_2644_);
    leanh::lean_dec_ref(v_a_2643_);
    return v_res_2648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(
    mut v_00_u03c3_2649_: *mut leanh::LeanObject,
    mut v_mvarId_2650_: *mut leanh::LeanObject,
    mut v_mkName_2651_: *mut leanh::LeanObject,
    mut v_i_2652_: *mut leanh::LeanObject,
    mut v_lctx_2653_: *mut leanh::LeanObject,
    mut v_fvars_2654_: *mut leanh::LeanObject,
    mut v_j_2655_: *mut leanh::LeanObject,
    mut v_s_2656_: *mut leanh::LeanObject,
    mut v_type_2657_: *mut leanh::LeanObject,
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
    mut v_a_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2663_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(
        v_mvarId_2650_,
        v_mkName_2651_,
        v_i_2652_,
        v_lctx_2653_,
        v_fvars_2654_,
        v_j_2655_,
        v_s_2656_,
        v_type_2657_,
        v_a_2658_,
        v_a_2659_,
        v_a_2660_,
        v_a_2661_,
    );
    return v___x_2663_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___boxed(
    mut v_00_u03c3_2664_: *mut leanh::LeanObject,
    mut v_mvarId_2665_: *mut leanh::LeanObject,
    mut v_mkName_2666_: *mut leanh::LeanObject,
    mut v_i_2667_: *mut leanh::LeanObject,
    mut v_lctx_2668_: *mut leanh::LeanObject,
    mut v_fvars_2669_: *mut leanh::LeanObject,
    mut v_j_2670_: *mut leanh::LeanObject,
    mut v_s_2671_: *mut leanh::LeanObject,
    mut v_type_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
    mut v_a_2675_: *mut leanh::LeanObject,
    mut v_a_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(
        v_00_u03c3_2664_,
        v_mvarId_2665_,
        v_mkName_2666_,
        v_i_2667_,
        v_lctx_2668_,
        v_fvars_2669_,
        v_j_2670_,
        v_s_2671_,
        v_type_2672_,
        v_a_2673_,
        v_a_2674_,
        v_a_2675_,
        v_a_2676_,
    );
    leanh::lean_dec(v_a_2676_);
    leanh::lean_dec_ref(v_a_2675_);
    leanh::lean_dec(v_a_2674_);
    leanh::lean_dec_ref(v_a_2673_);
    return v_res_2678_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(
    mut v_mvarId_2700_: *mut leanh::LeanObject,
    mut v___x_2701_: *mut leanh::LeanObject,
    mut v_mkName_2702_: *mut leanh::LeanObject,
    mut v_n_2703_: *mut leanh::LeanObject,
    mut v_s_2704_: *mut leanh::LeanObject,
    mut v___f_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
    mut v___y_2708_: *mut leanh::LeanObject,
    mut v___y_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v_fst_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2728_: usize = 0;
    let mut v___x_2729_: usize = 0;
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_a_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2754_: u8 = 0;
    let mut v_a_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_2700_);
                v___x_2711_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2700_,
                    v___x_2701_,
                    v___y_2706_,
                    v___y_2707_,
                    v___y_2708_,
                    v___y_2709_,
                );
                if leanh::lean_obj_tag(v___x_2711_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2711_, 1);
                    leanh::lean_inc(v_mvarId_2700_);
                    v___x_2712_ = l_Lean_MVarId_getType(
                        v_mvarId_2700_,
                        v___y_2706_,
                        v___y_2707_,
                        v___y_2708_,
                        v___y_2709_,
                    );
                    if leanh::lean_obj_tag(v___x_2712_) == 0 {
                        v_a_2713_ = leanh::lean_ctor_get(v___x_2712_, 0);
                        leanh::lean_inc(v_a_2713_);
                        leanh::lean_dec_ref_known(v___x_2712_, 1);
                        v_lctx_2714_ = leanh::lean_ctor_get(v___y_2706_, 2);
                        leanh::lean_inc_ref(v_lctx_2714_);
                        v___x_2715_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2716_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0;
                        v___x_2717_ =
                            l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(
                                v_mvarId_2700_,
                                v_mkName_2702_,
                                v_n_2703_,
                                v_lctx_2714_,
                                v___x_2716_,
                                v___x_2715_,
                                v_s_2704_,
                                v_a_2713_,
                                v___y_2706_,
                                v___y_2707_,
                                v___y_2708_,
                                v___y_2709_,
                            );
                        leanh::lean_dec_ref(v___y_2706_);
                        if leanh::lean_obj_tag(v___x_2717_) == 0 {
                            v_a_2718_ = leanh::lean_ctor_get(v___x_2717_, 0);
                            v_isSharedCheck_2738_ =
                                (!leanh::lean_is_exclusive(v___x_2717_)) as u8;
                            if v_isSharedCheck_2738_ == 0 {
                                v___x_2720_ = v___x_2717_;
                                v_isShared_2721_ = v_isSharedCheck_2738_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2718_);
                                leanh::lean_dec(v___x_2717_);
                                v___x_2720_ = leanh::lean_box(0);
                                v_isShared_2721_ = v_isSharedCheck_2738_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___f_2705_);
                            v_a_2739_ = leanh::lean_ctor_get(v___x_2717_, 0);
                            v_isSharedCheck_2746_ =
                                (!leanh::lean_is_exclusive(v___x_2717_)) as u8;
                            if v_isSharedCheck_2746_ == 0 {
                                v___x_2741_ = v___x_2717_;
                                v_isShared_2742_ = v_isSharedCheck_2746_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2739_);
                                leanh::lean_dec(v___x_2717_);
                                v___x_2741_ = leanh::lean_box(0);
                                v_isShared_2742_ = v_isSharedCheck_2746_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_2706_);
                        leanh::lean_dec_ref(v___f_2705_);
                        leanh::lean_dec(v_s_2704_);
                        leanh::lean_dec(v_n_2703_);
                        leanh::lean_dec_ref(v_mkName_2702_);
                        leanh::lean_dec(v_mvarId_2700_);
                        v_a_2747_ = leanh::lean_ctor_get(v___x_2712_, 0);
                        v_isSharedCheck_2754_ =
                            (!leanh::lean_is_exclusive(v___x_2712_)) as u8;
                        if v_isSharedCheck_2754_ == 0 {
                            v___x_2749_ = v___x_2712_;
                            v_isShared_2750_ = v_isSharedCheck_2754_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2747_);
                            leanh::lean_dec(v___x_2712_);
                            v___x_2749_ = leanh::lean_box(0);
                            v_isShared_2750_ = v_isSharedCheck_2754_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2706_);
                    leanh::lean_dec_ref(v___f_2705_);
                    leanh::lean_dec(v_s_2704_);
                    leanh::lean_dec(v_n_2703_);
                    leanh::lean_dec_ref(v_mkName_2702_);
                    leanh::lean_dec(v_mvarId_2700_);
                    v_a_2755_ = leanh::lean_ctor_get(v___x_2711_, 0);
                    v_isSharedCheck_2762_ = (!leanh::lean_is_exclusive(v___x_2711_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v___x_2711_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2755_);
                        leanh::lean_dec(v___x_2711_);
                        v___x_2757_ = leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2722_ = leanh::lean_ctor_get(v_a_2718_, 0);
                v_snd_2723_ = leanh::lean_ctor_get(v_a_2718_, 1);
                v_isSharedCheck_2737_ = (!leanh::lean_is_exclusive(v_a_2718_)) as u8;
                if v_isSharedCheck_2737_ == 0 {
                    v___x_2725_ = v_a_2718_;
                    v_isShared_2726_ = v_isSharedCheck_2737_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2723_);
                    leanh::lean_inc(v_fst_2722_);
                    leanh::lean_dec(v_a_2718_);
                    v___x_2725_ = leanh::lean_box(0);
                    v_isShared_2726_ = v_isSharedCheck_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2727_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10;
                v_sz_2728_ = lean_array_size(v_fst_2722_);
                v___x_2729_ = 0usize;
                v___x_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2727_,
                    v___f_2705_,
                    v_sz_2728_,
                    v___x_2729_,
                    v_fst_2722_,
                );
                if v_isShared_2726_ == 0 {
                    leanh::lean_ctor_set(v___x_2725_, 0, v___x_2730_);
                    v___x_2732_ = v___x_2725_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_snd_2723_);
                    v___x_2732_ = v_reuseFailAlloc_2736_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2721_ == 0 {
                    leanh::lean_ctor_set(v___x_2720_, 0, v___x_2732_);
                    v___x_2734_ = v___x_2720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
                    v___x_2734_ = v_reuseFailAlloc_2735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2734_;
            }
            5 => {
                if v_isShared_2742_ == 0 {
                    v___x_2744_ = v___x_2741_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2744_;
            }
            7 => {
                if v_isShared_2750_ == 0 {
                    v___x_2752_ = v___x_2749_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2753_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
                    v___x_2752_ = v_reuseFailAlloc_2753_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2752_;
            }
            9 => {
                if v_isShared_2758_ == 0 {
                    v___x_2760_ = v___x_2757_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed(
    mut v_mvarId_2763_: *mut leanh::LeanObject,
    mut v___x_2764_: *mut leanh::LeanObject,
    mut v_mkName_2765_: *mut leanh::LeanObject,
    mut v_n_2766_: *mut leanh::LeanObject,
    mut v_s_2767_: *mut leanh::LeanObject,
    mut v___f_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(
        v_mvarId_2763_,
        v___x_2764_,
        v_mkName_2765_,
        v_n_2766_,
        v_s_2767_,
        v___f_2768_,
        v___y_2769_,
        v___y_2770_,
        v___y_2771_,
        v___y_2772_,
    );
    leanh::lean_dec(v___y_2772_);
    leanh::lean_dec_ref(v___y_2771_);
    leanh::lean_dec(v___y_2770_);
    return v_res_2774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(
    mut v_mvarId_2776_: *mut leanh::LeanObject,
    mut v_n_2777_: *mut leanh::LeanObject,
    mut v_mkName_2778_: *mut leanh::LeanObject,
    mut v_s_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v_toFunctor_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___f_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43__overap_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_unused_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2785_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
                v_toApplicative_2786_ = leanh::lean_ctor_get(v___x_2785_, 0);
                v_toFunctor_2787_ = leanh::lean_ctor_get(v_toApplicative_2786_, 0);
                v_toSeq_2788_ = leanh::lean_ctor_get(v_toApplicative_2786_, 2);
                v_toSeqLeft_2789_ = leanh::lean_ctor_get(v_toApplicative_2786_, 3);
                v_toSeqRight_2790_ = leanh::lean_ctor_get(v_toApplicative_2786_, 4);
                v___f_2791_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2;
                v___f_2792_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2787_, 2);
                v___f_2793_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2793_, 0, v_toFunctor_2787_);
                v___f_2794_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2794_, 0, v_toFunctor_2787_);
                v___x_2795_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2795_, 0, v___f_2793_);
                leanh::lean_ctor_set(v___x_2795_, 1, v___f_2794_);
                leanh::lean_inc(v_toSeqRight_2790_);
                v___f_2796_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2796_, 0, v_toSeqRight_2790_);
                leanh::lean_inc(v_toSeqLeft_2789_);
                v___f_2797_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2797_, 0, v_toSeqLeft_2789_);
                leanh::lean_inc(v_toSeq_2788_);
                v___f_2798_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2798_, 0, v_toSeq_2788_);
                v___x_2799_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2799_, 0, v___x_2795_);
                leanh::lean_ctor_set(v___x_2799_, 1, v___f_2791_);
                leanh::lean_ctor_set(v___x_2799_, 2, v___f_2798_);
                leanh::lean_ctor_set(v___x_2799_, 3, v___f_2797_);
                leanh::lean_ctor_set(v___x_2799_, 4, v___f_2796_);
                v___x_2800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2800_, 0, v___x_2799_);
                leanh::lean_ctor_set(v___x_2800_, 1, v___f_2792_);
                v___x_2801_ = l_StateRefT_x27_instMonad___redArg(v___x_2800_);
                v___x_2802_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2802_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2802_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2802_, 2, v___x_2801_);
                v___x_2803_ = l_instMonadControlTOfPure___redArg(v___x_2802_);
                v_toApplicative_2804_ = leanh::lean_ctor_get(v___x_2785_, 0);
                v_toFunctor_2805_ = leanh::lean_ctor_get(v_toApplicative_2804_, 0);
                v_toSeq_2806_ = leanh::lean_ctor_get(v_toApplicative_2804_, 2);
                v_toSeqLeft_2807_ = leanh::lean_ctor_get(v_toApplicative_2804_, 3);
                v_toSeqRight_2808_ = leanh::lean_ctor_get(v_toApplicative_2804_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2805_, 2);
                v___f_2809_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2809_, 0, v_toFunctor_2805_);
                v___f_2810_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2810_, 0, v_toFunctor_2805_);
                v___x_2811_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2811_, 0, v___f_2809_);
                leanh::lean_ctor_set(v___x_2811_, 1, v___f_2810_);
                leanh::lean_inc(v_toSeqRight_2808_);
                v___f_2812_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2812_, 0, v_toSeqRight_2808_);
                leanh::lean_inc(v_toSeqLeft_2807_);
                v___f_2813_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2813_, 0, v_toSeqLeft_2807_);
                leanh::lean_inc(v_toSeq_2806_);
                v___f_2814_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2814_, 0, v_toSeq_2806_);
                v___x_2815_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2815_, 0, v___x_2811_);
                leanh::lean_ctor_set(v___x_2815_, 1, v___f_2791_);
                leanh::lean_ctor_set(v___x_2815_, 2, v___f_2814_);
                leanh::lean_ctor_set(v___x_2815_, 3, v___f_2813_);
                leanh::lean_ctor_set(v___x_2815_, 4, v___f_2812_);
                v___x_2816_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                leanh::lean_ctor_set(v___x_2816_, 1, v___f_2792_);
                v___x_2817_ = l_StateRefT_x27_instMonad___redArg(v___x_2816_);
                v_toApplicative_2818_ = leanh::lean_ctor_get(v___x_2817_, 0);
                v_isSharedCheck_2850_ = (!leanh::lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2850_ == 0 {
                    v_unused_2851_ = leanh::lean_ctor_get(v___x_2817_, 1);
                    leanh::lean_dec(v_unused_2851_);
                    v___x_2820_ = v___x_2817_;
                    v_isShared_2821_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2818_);
                    leanh::lean_dec(v___x_2817_);
                    v___x_2820_ = leanh::lean_box(0);
                    v_isShared_2821_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2822_ = leanh::lean_ctor_get(v_toApplicative_2818_, 0);
                v_toSeq_2823_ = leanh::lean_ctor_get(v_toApplicative_2818_, 2);
                v_toSeqLeft_2824_ = leanh::lean_ctor_get(v_toApplicative_2818_, 3);
                v_toSeqRight_2825_ = leanh::lean_ctor_get(v_toApplicative_2818_, 4);
                v_isSharedCheck_2848_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2818_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v_unused_2849_ = leanh::lean_ctor_get(v_toApplicative_2818_, 1);
                    leanh::lean_dec(v_unused_2849_);
                    v___x_2827_ = v_toApplicative_2818_;
                    v_isShared_2828_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2825_);
                    leanh::lean_inc(v_toSeqLeft_2824_);
                    leanh::lean_inc(v_toSeq_2823_);
                    leanh::lean_inc(v_toFunctor_2822_);
                    leanh::lean_dec(v_toApplicative_2818_);
                    v___x_2827_ = leanh::lean_box(0);
                    v_isShared_2828_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2829_ =
                    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0;
                v___f_2830_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4;
                v___f_2831_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_2822_);
                v___f_2832_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2832_, 0, v_toFunctor_2822_);
                v___f_2833_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2833_, 0, v_toFunctor_2822_);
                v___x_2834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2834_, 0, v___f_2832_);
                leanh::lean_ctor_set(v___x_2834_, 1, v___f_2833_);
                v___f_2835_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2835_, 0, v_toSeqRight_2825_);
                v___f_2836_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2836_, 0, v_toSeqLeft_2824_);
                v___f_2837_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2837_, 0, v_toSeq_2823_);
                if v_isShared_2828_ == 0 {
                    leanh::lean_ctor_set(v___x_2827_, 4, v___f_2835_);
                    leanh::lean_ctor_set(v___x_2827_, 3, v___f_2836_);
                    leanh::lean_ctor_set(v___x_2827_, 2, v___f_2837_);
                    leanh::lean_ctor_set(v___x_2827_, 1, v___f_2830_);
                    leanh::lean_ctor_set(v___x_2827_, 0, v___x_2834_);
                    v___x_2839_ = v___x_2827_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___f_2830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 2, v___f_2837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 3, v___f_2836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 4, v___f_2835_);
                    v___x_2839_ = v_reuseFailAlloc_2847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2821_ == 0 {
                    leanh::lean_ctor_set(v___x_2820_, 1, v___f_2831_);
                    leanh::lean_ctor_set(v___x_2820_, 0, v___x_2839_);
                    v___x_2841_ = v___x_2820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___f_2831_);
                    v___x_2841_ = v_reuseFailAlloc_2846_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2842_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                leanh::lean_inc(v_mvarId_2776_);
                v___f_2843_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                leanh::lean_closure_set(v___f_2843_, 0, v_mvarId_2776_);
                leanh::lean_closure_set(v___f_2843_, 1, v___x_2842_);
                leanh::lean_closure_set(v___f_2843_, 2, v_mkName_2778_);
                leanh::lean_closure_set(v___f_2843_, 3, v_n_2777_);
                leanh::lean_closure_set(v___f_2843_, 4, v_s_2779_);
                leanh::lean_closure_set(v___f_2843_, 5, v___f_2829_);
                v___x_43__overap_2844_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2803_,
                    v___x_2841_,
                    v_mvarId_2776_,
                    v___f_2843_,
                );
                leanh::lean_inc(v_a_2783_);
                leanh::lean_inc_ref(v_a_2782_);
                leanh::lean_inc(v_a_2781_);
                leanh::lean_inc_ref(v_a_2780_);
                v___x_2845_ = leanh::lean_apply_5(
                    v___x_43__overap_2844_,
                    v_a_2780_,
                    v_a_2781_,
                    v_a_2782_,
                    v_a_2783_,
                    leanh::lean_box(0),
                );
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(
    mut v_mvarId_2852_: *mut leanh::LeanObject,
    mut v_n_2853_: *mut leanh::LeanObject,
    mut v_mkName_2854_: *mut leanh::LeanObject,
    mut v_s_2855_: *mut leanh::LeanObject,
    mut v_a_2856_: *mut leanh::LeanObject,
    mut v_a_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2861_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(
        v_mvarId_2852_,
        v_n_2853_,
        v_mkName_2854_,
        v_s_2855_,
        v_a_2856_,
        v_a_2857_,
        v_a_2858_,
        v_a_2859_,
    );
    leanh::lean_dec(v_a_2859_);
    leanh::lean_dec_ref(v_a_2858_);
    leanh::lean_dec(v_a_2857_);
    leanh::lean_dec_ref(v_a_2856_);
    return v_res_2861_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(
    mut v_00_u03c3_2862_: *mut leanh::LeanObject,
    mut v_mvarId_2863_: *mut leanh::LeanObject,
    mut v_n_2864_: *mut leanh::LeanObject,
    mut v_mkName_2865_: *mut leanh::LeanObject,
    mut v_s_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v_toFunctor_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___f_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617__overap_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_unused_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut v_unused_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2872_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
                v_toApplicative_2873_ = leanh::lean_ctor_get(v___x_2872_, 0);
                v_toFunctor_2874_ = leanh::lean_ctor_get(v_toApplicative_2873_, 0);
                v_toSeq_2875_ = leanh::lean_ctor_get(v_toApplicative_2873_, 2);
                v_toSeqLeft_2876_ = leanh::lean_ctor_get(v_toApplicative_2873_, 3);
                v_toSeqRight_2877_ = leanh::lean_ctor_get(v_toApplicative_2873_, 4);
                v___f_2878_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2;
                v___f_2879_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2874_, 2);
                v___f_2880_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2880_, 0, v_toFunctor_2874_);
                v___f_2881_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2881_, 0, v_toFunctor_2874_);
                v___x_2882_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2882_, 0, v___f_2880_);
                leanh::lean_ctor_set(v___x_2882_, 1, v___f_2881_);
                leanh::lean_inc(v_toSeqRight_2877_);
                v___f_2883_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2883_, 0, v_toSeqRight_2877_);
                leanh::lean_inc(v_toSeqLeft_2876_);
                v___f_2884_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2884_, 0, v_toSeqLeft_2876_);
                leanh::lean_inc(v_toSeq_2875_);
                v___f_2885_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2885_, 0, v_toSeq_2875_);
                v___x_2886_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2886_, 0, v___x_2882_);
                leanh::lean_ctor_set(v___x_2886_, 1, v___f_2878_);
                leanh::lean_ctor_set(v___x_2886_, 2, v___f_2885_);
                leanh::lean_ctor_set(v___x_2886_, 3, v___f_2884_);
                leanh::lean_ctor_set(v___x_2886_, 4, v___f_2883_);
                v___x_2887_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2887_, 0, v___x_2886_);
                leanh::lean_ctor_set(v___x_2887_, 1, v___f_2879_);
                v___x_2888_ = l_StateRefT_x27_instMonad___redArg(v___x_2887_);
                v___x_2889_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2889_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2889_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2889_, 2, v___x_2888_);
                v___x_2890_ = l_instMonadControlTOfPure___redArg(v___x_2889_);
                v_toApplicative_2891_ = leanh::lean_ctor_get(v___x_2872_, 0);
                v_toFunctor_2892_ = leanh::lean_ctor_get(v_toApplicative_2891_, 0);
                v_toSeq_2893_ = leanh::lean_ctor_get(v_toApplicative_2891_, 2);
                v_toSeqLeft_2894_ = leanh::lean_ctor_get(v_toApplicative_2891_, 3);
                v_toSeqRight_2895_ = leanh::lean_ctor_get(v_toApplicative_2891_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2892_, 2);
                v___f_2896_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2896_, 0, v_toFunctor_2892_);
                v___f_2897_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2897_, 0, v_toFunctor_2892_);
                v___x_2898_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2898_, 0, v___f_2896_);
                leanh::lean_ctor_set(v___x_2898_, 1, v___f_2897_);
                leanh::lean_inc(v_toSeqRight_2895_);
                v___f_2899_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2899_, 0, v_toSeqRight_2895_);
                leanh::lean_inc(v_toSeqLeft_2894_);
                v___f_2900_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2900_, 0, v_toSeqLeft_2894_);
                leanh::lean_inc(v_toSeq_2893_);
                v___f_2901_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2901_, 0, v_toSeq_2893_);
                v___x_2902_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2902_, 0, v___x_2898_);
                leanh::lean_ctor_set(v___x_2902_, 1, v___f_2878_);
                leanh::lean_ctor_set(v___x_2902_, 2, v___f_2901_);
                leanh::lean_ctor_set(v___x_2902_, 3, v___f_2900_);
                leanh::lean_ctor_set(v___x_2902_, 4, v___f_2899_);
                v___x_2903_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2903_, 0, v___x_2902_);
                leanh::lean_ctor_set(v___x_2903_, 1, v___f_2879_);
                v___x_2904_ = l_StateRefT_x27_instMonad___redArg(v___x_2903_);
                v_toApplicative_2905_ = leanh::lean_ctor_get(v___x_2904_, 0);
                v_isSharedCheck_2937_ = (!leanh::lean_is_exclusive(v___x_2904_)) as u8;
                if v_isSharedCheck_2937_ == 0 {
                    v_unused_2938_ = leanh::lean_ctor_get(v___x_2904_, 1);
                    leanh::lean_dec(v_unused_2938_);
                    v___x_2907_ = v___x_2904_;
                    v_isShared_2908_ = v_isSharedCheck_2937_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2905_);
                    leanh::lean_dec(v___x_2904_);
                    v___x_2907_ = leanh::lean_box(0);
                    v_isShared_2908_ = v_isSharedCheck_2937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2909_ = leanh::lean_ctor_get(v_toApplicative_2905_, 0);
                v_toSeq_2910_ = leanh::lean_ctor_get(v_toApplicative_2905_, 2);
                v_toSeqLeft_2911_ = leanh::lean_ctor_get(v_toApplicative_2905_, 3);
                v_toSeqRight_2912_ = leanh::lean_ctor_get(v_toApplicative_2905_, 4);
                v_isSharedCheck_2935_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2905_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v_unused_2936_ = leanh::lean_ctor_get(v_toApplicative_2905_, 1);
                    leanh::lean_dec(v_unused_2936_);
                    v___x_2914_ = v_toApplicative_2905_;
                    v_isShared_2915_ = v_isSharedCheck_2935_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2912_);
                    leanh::lean_inc(v_toSeqLeft_2911_);
                    leanh::lean_inc(v_toSeq_2910_);
                    leanh::lean_inc(v_toFunctor_2909_);
                    leanh::lean_dec(v_toApplicative_2905_);
                    v___x_2914_ = leanh::lean_box(0);
                    v_isShared_2915_ = v_isSharedCheck_2935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2916_ =
                    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0;
                v___f_2917_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4;
                v___f_2918_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_2909_);
                v___f_2919_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2919_, 0, v_toFunctor_2909_);
                v___f_2920_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2920_, 0, v_toFunctor_2909_);
                v___x_2921_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2921_, 0, v___f_2919_);
                leanh::lean_ctor_set(v___x_2921_, 1, v___f_2920_);
                v___f_2922_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2922_, 0, v_toSeqRight_2912_);
                v___f_2923_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2923_, 0, v_toSeqLeft_2911_);
                v___f_2924_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2924_, 0, v_toSeq_2910_);
                if v_isShared_2915_ == 0 {
                    leanh::lean_ctor_set(v___x_2914_, 4, v___f_2922_);
                    leanh::lean_ctor_set(v___x_2914_, 3, v___f_2923_);
                    leanh::lean_ctor_set(v___x_2914_, 2, v___f_2924_);
                    leanh::lean_ctor_set(v___x_2914_, 1, v___f_2917_);
                    leanh::lean_ctor_set(v___x_2914_, 0, v___x_2921_);
                    v___x_2926_ = v___x_2914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 1, v___f_2917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 2, v___f_2924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 3, v___f_2923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 4, v___f_2922_);
                    v___x_2926_ = v_reuseFailAlloc_2934_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2908_ == 0 {
                    leanh::lean_ctor_set(v___x_2907_, 1, v___f_2918_);
                    leanh::lean_ctor_set(v___x_2907_, 0, v___x_2926_);
                    v___x_2928_ = v___x_2907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___f_2918_);
                    v___x_2928_ = v_reuseFailAlloc_2933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2929_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                leanh::lean_inc(v_mvarId_2863_);
                v___f_2930_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                leanh::lean_closure_set(v___f_2930_, 0, v_mvarId_2863_);
                leanh::lean_closure_set(v___f_2930_, 1, v___x_2929_);
                leanh::lean_closure_set(v___f_2930_, 2, v_mkName_2865_);
                leanh::lean_closure_set(v___f_2930_, 3, v_n_2864_);
                leanh::lean_closure_set(v___f_2930_, 4, v_s_2866_);
                leanh::lean_closure_set(v___f_2930_, 5, v___f_2916_);
                v___x_617__overap_2931_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2890_,
                    v___x_2928_,
                    v_mvarId_2863_,
                    v___f_2930_,
                );
                leanh::lean_inc(v_a_2870_);
                leanh::lean_inc_ref(v_a_2869_);
                leanh::lean_inc(v_a_2868_);
                leanh::lean_inc_ref(v_a_2867_);
                v___x_2932_ = leanh::lean_apply_5(
                    v___x_617__overap_2931_,
                    v_a_2867_,
                    v_a_2868_,
                    v_a_2869_,
                    v_a_2870_,
                    leanh::lean_box(0),
                );
                return v___x_2932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(
    mut v_00_u03c3_2939_: *mut leanh::LeanObject,
    mut v_mvarId_2940_: *mut leanh::LeanObject,
    mut v_n_2941_: *mut leanh::LeanObject,
    mut v_mkName_2942_: *mut leanh::LeanObject,
    mut v_s_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
    mut v_a_2945_: *mut leanh::LeanObject,
    mut v_a_2946_: *mut leanh::LeanObject,
    mut v_a_2947_: *mut leanh::LeanObject,
    mut v_a_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(
        v_00_u03c3_2939_,
        v_mvarId_2940_,
        v_n_2941_,
        v_mkName_2942_,
        v_s_2943_,
        v_a_2944_,
        v_a_2945_,
        v_a_2946_,
        v_a_2947_,
    );
    leanh::lean_dec(v_a_2947_);
    leanh::lean_dec_ref(v_a_2946_);
    leanh::lean_dec(v_a_2945_);
    leanh::lean_dec_ref(v_a_2944_);
    return v_res_2949_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(
    mut v_name_2950_: *mut leanh::LeanObject,
    mut v_decl_2951_: *mut leanh::LeanObject,
    mut v_ref_2952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2954_ = leanh::lean_ctor_get(v_decl_2951_, 0);
                v_descr_2955_ = leanh::lean_ctor_get(v_decl_2951_, 1);
                v_deprecation_x3f_2956_ = leanh::lean_ctor_get(v_decl_2951_, 2);
                v___x_2957_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2958_ = (leanh::lean_unbox(v_defValue_2954_) as u8);
                leanh::lean_ctor_set_uint8(v___x_2957_, 0 as u32, v___x_2958_);
                leanh::lean_inc(v_deprecation_x3f_2956_);
                leanh::lean_inc_ref(v_descr_2955_);
                leanh::lean_inc_n(v_name_2950_, 2);
                v___x_2959_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2959_, 0, v_name_2950_);
                leanh::lean_ctor_set(v___x_2959_, 1, v_ref_2952_);
                leanh::lean_ctor_set(v___x_2959_, 2, v___x_2957_);
                leanh::lean_ctor_set(v___x_2959_, 3, v_descr_2955_);
                leanh::lean_ctor_set(v___x_2959_, 4, v_deprecation_x3f_2956_);
                v___x_2960_ = lean_register_option(v_name_2950_, v___x_2959_);
                if leanh::lean_obj_tag(v___x_2960_) == 0 {
                    v_isSharedCheck_2968_ = (!leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v_unused_2969_ = leanh::lean_ctor_get(v___x_2960_, 0);
                        leanh::lean_dec(v_unused_2969_);
                        v___x_2962_ = v___x_2960_;
                        v_isShared_2963_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2960_);
                        v___x_2962_ = leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_2950_);
                    v_a_2970_ = leanh::lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2977_ = (!leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2977_ == 0 {
                        v___x_2972_ = v___x_2960_;
                        v_isShared_2973_ = v_isSharedCheck_2977_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2970_);
                        leanh::lean_dec(v___x_2960_);
                        v___x_2972_ = leanh::lean_box(0);
                        v_isShared_2973_ = v_isSharedCheck_2977_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_2954_);
                v___x_2964_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2964_, 0, v_name_2950_);
                leanh::lean_ctor_set(v___x_2964_, 1, v_defValue_2954_);
                if v_isShared_2963_ == 0 {
                    leanh::lean_ctor_set(v___x_2962_, 0, v___x_2964_);
                    v___x_2966_ = v___x_2962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
                    v___x_2966_ = v_reuseFailAlloc_2967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2966_;
            }
            3 => {
                if v_isShared_2973_ == 0 {
                    v___x_2975_ = v___x_2972_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2976_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
                    v___x_2975_ = v_reuseFailAlloc_2976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2978_: *mut leanh::LeanObject,
    mut v_decl_2979_: *mut leanh::LeanObject,
    mut v_ref_2980_: *mut leanh::LeanObject,
    mut v_a_2981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_2978_, v_decl_2979_, v_ref_2980_);
    leanh::lean_dec_ref(v_decl_2979_);
    return v_res_2982_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_;
    v___x_3003_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_;
    v___x_3004_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_;
    v___x_3005_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_3002_, v___x_3003_, v___x_3004_);
    return v___x_3005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(
    mut v_a_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3007_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
    return v_res_3007_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(
    mut v_lctx_3008_: *mut leanh::LeanObject,
    mut v_binderName_3009_: *mut leanh::LeanObject,
    mut v_hygienic_3010_: u8,
    mut v_a_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_hygienic_3010_ == 0 {
        let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3014_ = l_Lean_LocalContext_getUnusedName(v_lctx_3008_, v_binderName_3009_);
        v___x_3015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3015_, 0, v___x_3014_);
        return v___x_3015_;
    } else {
        let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3016_ = l_Lean_Core_mkFreshUserName(v_binderName_3009_, v_a_3011_, v_a_3012_);
        return v___x_3016_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(
    mut v_lctx_3017_: *mut leanh::LeanObject,
    mut v_binderName_3018_: *mut leanh::LeanObject,
    mut v_hygienic_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
    mut v_a_3021_: *mut leanh::LeanObject,
    mut v_a_3022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hygienic_boxed_3023_: u8 = 0;
    let mut v_res_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hygienic_boxed_3023_ = (leanh::lean_unbox(v_hygienic_3019_) as u8);
    v_res_3024_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(
            v_lctx_3017_,
            v_binderName_3018_,
            v_hygienic_boxed_3023_,
            v_a_3020_,
            v_a_3021_,
        );
    leanh::lean_dec(v_a_3021_);
    leanh::lean_dec_ref(v_a_3020_);
    leanh::lean_dec_ref(v_lctx_3017_);
    return v_res_3024_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(
    mut v_lctx_3025_: *mut leanh::LeanObject,
    mut v_binderName_3026_: *mut leanh::LeanObject,
    mut v_hygienic_3027_: u8,
    mut v_a_3028_: *mut leanh::LeanObject,
    mut v_a_3029_: *mut leanh::LeanObject,
    mut v_a_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3033_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(
            v_lctx_3025_,
            v_binderName_3026_,
            v_hygienic_3027_,
            v_a_3030_,
            v_a_3031_,
        );
    return v___x_3033_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___boxed(
    mut v_lctx_3034_: *mut leanh::LeanObject,
    mut v_binderName_3035_: *mut leanh::LeanObject,
    mut v_hygienic_3036_: *mut leanh::LeanObject,
    mut v_a_3037_: *mut leanh::LeanObject,
    mut v_a_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hygienic_boxed_3042_: u8 = 0;
    let mut v_res_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hygienic_boxed_3042_ = (leanh::lean_unbox(v_hygienic_3036_) as u8);
    v_res_3043_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(
        v_lctx_3034_,
        v_binderName_3035_,
        v_hygienic_boxed_3042_,
        v_a_3037_,
        v_a_3038_,
        v_a_3039_,
        v_a_3040_,
    );
    leanh::lean_dec(v_a_3040_);
    leanh::lean_dec_ref(v_a_3039_);
    leanh::lean_dec(v_a_3038_);
    leanh::lean_dec_ref(v_a_3037_);
    leanh::lean_dec_ref(v_lctx_3034_);
    return v_res_3043_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
    mut v_opts_3044_: *mut leanh::LeanObject,
    mut v_opt_3045_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3046_ = leanh::lean_ctor_get(v_opt_3045_, 0);
    v_defValue_3047_ = leanh::lean_ctor_get(v_opt_3045_, 1);
    v_map_3048_ = leanh::lean_ctor_get(v_opts_3044_, 0);
    v___x_3049_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3048_,
            v_name_3046_,
        );
    if leanh::lean_obj_tag(v___x_3049_) == 0 {
        let mut v___x_3050_: u8 = 0;
        v___x_3050_ = (leanh::lean_unbox(v_defValue_3047_) as u8);
        return v___x_3050_;
    } else {
        let mut v_val_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3051_ = leanh::lean_ctor_get(v___x_3049_, 0);
        leanh::lean_inc(v_val_3051_);
        leanh::lean_dec_ref_known(v___x_3049_, 1);
        if leanh::lean_obj_tag(v_val_3051_) == 1 {
            let mut v_v_3052_: u8 = 0;
            v_v_3052_ = leanh::lean_ctor_get_uint8(v_val_3051_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3051_, 0);
            return v_v_3052_;
        } else {
            let mut v___x_3053_: u8 = 0;
            leanh::lean_dec(v_val_3051_);
            v___x_3053_ = (leanh::lean_unbox(v_defValue_3047_) as u8);
            return v___x_3053_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(
    mut v_opts_3054_: *mut leanh::LeanObject,
    mut v_opt_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
        v_opts_3054_,
        v_opt_3055_,
    );
    leanh::lean_dec_ref(v_opt_3055_);
    leanh::lean_dec_ref(v_opts_3054_);
    v_r_3057_ = leanh::lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic___redArg(
    mut v_binderName_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
    mut v_a_3060_: *mut leanh::LeanObject,
    mut v_a_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_3063_ = leanh::lean_ctor_get(v_a_3059_, 2);
    v_options_3064_ = leanh::lean_ctor_get(v_a_3060_, 2);
    v___x_3065_ = l_Lean_Meta_tactic_hygienic;
    v___x_3066_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
        v_options_3064_,
        v___x_3065_,
    );
    v___x_3067_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(
            v_lctx_3063_,
            v_binderName_3058_,
            v___x_3066_,
            v_a_3060_,
            v_a_3061_,
        );
    return v___x_3067_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic___redArg___boxed(
    mut v_binderName_3068_: *mut leanh::LeanObject,
    mut v_a_3069_: *mut leanh::LeanObject,
    mut v_a_3070_: *mut leanh::LeanObject,
    mut v_a_3071_: *mut leanh::LeanObject,
    mut v_a_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(
        v_binderName_3068_,
        v_a_3069_,
        v_a_3070_,
        v_a_3071_,
    );
    leanh::lean_dec(v_a_3071_);
    leanh::lean_dec_ref(v_a_3070_);
    leanh::lean_dec_ref(v_a_3069_);
    return v_res_3073_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic(
    mut v_binderName_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(
        v_binderName_3074_,
        v_a_3075_,
        v_a_3077_,
        v_a_3078_,
    );
    return v___x_3080_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic___boxed(
    mut v_binderName_3081_: *mut leanh::LeanObject,
    mut v_a_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
    mut v_a_3084_: *mut leanh::LeanObject,
    mut v_a_3085_: *mut leanh::LeanObject,
    mut v_a_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Lean_Meta_mkFreshBinderNameForTactic(
        v_binderName_3081_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
    );
    leanh::lean_dec(v_a_3085_);
    leanh::lean_dec_ref(v_a_3084_);
    leanh::lean_dec(v_a_3083_);
    leanh::lean_dec_ref(v_a_3082_);
    return v_res_3087_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(
    mut v_preserveBinderNames_3091_: u8,
    mut v_hygienic_3092_: u8,
    mut v_lctx_3093_: *mut leanh::LeanObject,
    mut v_binderName_3094_: *mut leanh::LeanObject,
    mut v_rest_3095_: *mut leanh::LeanObject,
    mut v_a_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_a_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3123_ = l_Lean_Name_isAnonymous(v_binderName_3094_);
                if v___x_3123_ == 0 {
                    v_binderName_3100_ = v_binderName_3094_;
                    v___y_3101_ = v_a_3096_;
                    v___y_3102_ = v_a_3097_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_binderName_3094_);
                    v___x_3124_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1;
                    v___x_3125_ = l_Lean_Core_mkFreshUserName(v___x_3124_, v_a_3096_, v_a_3097_);
                    if leanh::lean_obj_tag(v___x_3125_) == 0 {
                        v_a_3126_ = leanh::lean_ctor_get(v___x_3125_, 0);
                        leanh::lean_inc(v_a_3126_);
                        leanh::lean_dec_ref_known(v___x_3125_, 1);
                        v_binderName_3100_ = v_a_3126_;
                        v___y_3101_ = v_a_3096_;
                        v___y_3102_ = v_a_3097_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_rest_3095_);
                        v_a_3127_ = leanh::lean_ctor_get(v___x_3125_, 0);
                        v_isSharedCheck_3134_ =
                            (!leanh::lean_is_exclusive(v___x_3125_)) as u8;
                        if v_isSharedCheck_3134_ == 0 {
                            v___x_3129_ = v___x_3125_;
                            v_isShared_3130_ = v_isSharedCheck_3134_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3127_);
                            leanh::lean_dec(v___x_3125_);
                            v___x_3129_ = leanh::lean_box(0);
                            v_isShared_3130_ = v_isSharedCheck_3134_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_preserveBinderNames_3091_ == 0 {
                    v___x_3103_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(v_lctx_3093_, v_binderName_3100_, v_hygienic_3092_, v___y_3101_, v___y_3102_);
                    if leanh::lean_obj_tag(v___x_3103_) == 0 {
                        v_a_3104_ = leanh::lean_ctor_get(v___x_3103_, 0);
                        v_isSharedCheck_3112_ =
                            (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                        if v_isSharedCheck_3112_ == 0 {
                            v___x_3106_ = v___x_3103_;
                            v_isShared_3107_ = v_isSharedCheck_3112_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3104_);
                            leanh::lean_dec(v___x_3103_);
                            v___x_3106_ = leanh::lean_box(0);
                            v_isShared_3107_ = v_isSharedCheck_3112_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_rest_3095_);
                        v_a_3113_ = leanh::lean_ctor_get(v___x_3103_, 0);
                        v_isSharedCheck_3120_ =
                            (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                        if v_isSharedCheck_3120_ == 0 {
                            v___x_3115_ = v___x_3103_;
                            v_isShared_3116_ = v_isSharedCheck_3120_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3113_);
                            leanh::lean_dec(v___x_3103_);
                            v___x_3115_ = leanh::lean_box(0);
                            v_isShared_3116_ = v_isSharedCheck_3120_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_3121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3121_, 0, v_binderName_3100_);
                    leanh::lean_ctor_set(v___x_3121_, 1, v_rest_3095_);
                    v___x_3122_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3122_, 0, v___x_3121_);
                    return v___x_3122_;
                }
            }
            2 => {
                v___x_3108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3108_, 0, v_a_3104_);
                leanh::lean_ctor_set(v___x_3108_, 1, v_rest_3095_);
                if v_isShared_3107_ == 0 {
                    leanh::lean_ctor_set(v___x_3106_, 0, v___x_3108_);
                    v___x_3110_ = v___x_3106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
                    v___x_3110_ = v_reuseFailAlloc_3111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3110_;
            }
            4 => {
                if v_isShared_3116_ == 0 {
                    v___x_3118_ = v___x_3115_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3118_;
            }
            6 => {
                if v_isShared_3130_ == 0 {
                    v___x_3132_ = v___x_3129_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___boxed(
    mut v_preserveBinderNames_3135_: *mut leanh::LeanObject,
    mut v_hygienic_3136_: *mut leanh::LeanObject,
    mut v_lctx_3137_: *mut leanh::LeanObject,
    mut v_binderName_3138_: *mut leanh::LeanObject,
    mut v_rest_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3143_: u8 = 0;
    let mut v_hygienic_boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3143_ =
        (leanh::lean_unbox(v_preserveBinderNames_3135_) as u8);
    v_hygienic_boxed_3144_ = (leanh::lean_unbox(v_hygienic_3136_) as u8);
    v_res_3145_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_3143_, v_hygienic_boxed_3144_, v_lctx_3137_, v_binderName_3138_, v_rest_3139_, v_a_3140_, v_a_3141_);
    leanh::lean_dec(v_a_3141_);
    leanh::lean_dec_ref(v_a_3140_);
    leanh::lean_dec_ref(v_lctx_3137_);
    return v_res_3145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(
    mut v_preserveBinderNames_3146_: u8,
    mut v_hygienic_3147_: u8,
    mut v_lctx_3148_: *mut leanh::LeanObject,
    mut v_binderName_3149_: *mut leanh::LeanObject,
    mut v_rest_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3156_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3146_, v_hygienic_3147_, v_lctx_3148_, v_binderName_3149_, v_rest_3150_, v_a_3153_, v_a_3154_);
    return v___x_3156_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(
    mut v_preserveBinderNames_3157_: *mut leanh::LeanObject,
    mut v_hygienic_3158_: *mut leanh::LeanObject,
    mut v_lctx_3159_: *mut leanh::LeanObject,
    mut v_binderName_3160_: *mut leanh::LeanObject,
    mut v_rest_3161_: *mut leanh::LeanObject,
    mut v_a_3162_: *mut leanh::LeanObject,
    mut v_a_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_a_3165_: *mut leanh::LeanObject,
    mut v_a_3166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3167_: u8 = 0;
    let mut v_hygienic_boxed_3168_: u8 = 0;
    let mut v_res_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3167_ =
        (leanh::lean_unbox(v_preserveBinderNames_3157_) as u8);
    v_hygienic_boxed_3168_ = (leanh::lean_unbox(v_hygienic_3158_) as u8);
    v_res_3169_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(
            v_preserveBinderNames_boxed_3167_,
            v_hygienic_boxed_3168_,
            v_lctx_3159_,
            v_binderName_3160_,
            v_rest_3161_,
            v_a_3162_,
            v_a_3163_,
            v_a_3164_,
            v_a_3165_,
        );
    leanh::lean_dec(v_a_3165_);
    leanh::lean_dec_ref(v_a_3164_);
    leanh::lean_dec(v_a_3163_);
    leanh::lean_dec_ref(v_a_3162_);
    leanh::lean_dec_ref(v_lctx_3159_);
    return v_res_3169_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(
    mut v_preserveBinderNames_3174_: u8,
    mut v_hygienic_3175_: u8,
    mut v_useNamesForExplicitOnly_3176_: u8,
    mut v_lctx_3177_: *mut leanh::LeanObject,
    mut v_binderName_3178_: *mut leanh::LeanObject,
    mut v_isExplicit_3179_: u8,
    mut v_x_3180_: *mut leanh::LeanObject,
    mut v_a_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3180_) == 0 {
                    v___x_3184_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3174_, v_hygienic_3175_, v_lctx_3177_, v_binderName_3178_, v_x_3180_, v_a_3181_, v_a_3182_);
                    return v___x_3184_;
                } else {
                    v_head_3185_ = leanh::lean_ctor_get(v_x_3180_, 0);
                    v_tail_3186_ = leanh::lean_ctor_get(v_x_3180_, 1);
                    if v_useNamesForExplicitOnly_3176_ == 0 {
                        leanh::lean_inc(v_tail_3186_);
                        leanh::lean_inc(v_head_3185_);
                        leanh::lean_dec_ref_known(v_x_3180_, 2);
                        state = 1;
                        continue;
                    } else {
                        if v_isExplicit_3179_ == 0 {
                            v___x_3193_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3174_, v_hygienic_3175_, v_lctx_3177_, v_binderName_3178_, v_x_3180_, v_a_3181_, v_a_3182_);
                            return v___x_3193_;
                        } else {
                            leanh::lean_inc(v_tail_3186_);
                            leanh::lean_inc(v_head_3185_);
                            leanh::lean_dec_ref_known(v_x_3180_, 2);
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3188_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1;
                v___x_3189_ = lean_name_eq(v_head_3185_, v___x_3188_);
                if v___x_3189_ == 0 {
                    leanh::lean_dec(v_binderName_3178_);
                    v___x_3190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3190_, 0, v_head_3185_);
                    leanh::lean_ctor_set(v___x_3190_, 1, v_tail_3186_);
                    v___x_3191_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3191_, 0, v___x_3190_);
                    return v___x_3191_;
                } else {
                    leanh::lean_dec(v_head_3185_);
                    v___x_3192_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3174_, v_hygienic_3175_, v_lctx_3177_, v_binderName_3178_, v_tail_3186_, v_a_3181_, v_a_3182_);
                    return v___x_3192_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(
    mut v_preserveBinderNames_3194_: *mut leanh::LeanObject,
    mut v_hygienic_3195_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3196_: *mut leanh::LeanObject,
    mut v_lctx_3197_: *mut leanh::LeanObject,
    mut v_binderName_3198_: *mut leanh::LeanObject,
    mut v_isExplicit_3199_: *mut leanh::LeanObject,
    mut v_x_3200_: *mut leanh::LeanObject,
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_a_3202_: *mut leanh::LeanObject,
    mut v_a_3203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3204_: u8 = 0;
    let mut v_hygienic_boxed_3205_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3206_: u8 = 0;
    let mut v_isExplicit_boxed_3207_: u8 = 0;
    let mut v_res_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3204_ =
        (leanh::lean_unbox(v_preserveBinderNames_3194_) as u8);
    v_hygienic_boxed_3205_ = (leanh::lean_unbox(v_hygienic_3195_) as u8);
    v_useNamesForExplicitOnly_boxed_3206_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_3196_) as u8);
    v_isExplicit_boxed_3207_ = (leanh::lean_unbox(v_isExplicit_3199_) as u8);
    v_res_3208_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(
        v_preserveBinderNames_boxed_3204_,
        v_hygienic_boxed_3205_,
        v_useNamesForExplicitOnly_boxed_3206_,
        v_lctx_3197_,
        v_binderName_3198_,
        v_isExplicit_boxed_3207_,
        v_x_3200_,
        v_a_3201_,
        v_a_3202_,
    );
    leanh::lean_dec(v_a_3202_);
    leanh::lean_dec_ref(v_a_3201_);
    leanh::lean_dec_ref(v_lctx_3197_);
    return v_res_3208_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(
    mut v_preserveBinderNames_3209_: u8,
    mut v_hygienic_3210_: u8,
    mut v_useNamesForExplicitOnly_3211_: u8,
    mut v_lctx_3212_: *mut leanh::LeanObject,
    mut v_binderName_3213_: *mut leanh::LeanObject,
    mut v_isExplicit_3214_: u8,
    mut v_x_3215_: *mut leanh::LeanObject,
    mut v_a_3216_: *mut leanh::LeanObject,
    mut v_a_3217_: *mut leanh::LeanObject,
    mut v_a_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3221_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(
        v_preserveBinderNames_3209_,
        v_hygienic_3210_,
        v_useNamesForExplicitOnly_3211_,
        v_lctx_3212_,
        v_binderName_3213_,
        v_isExplicit_3214_,
        v_x_3215_,
        v_a_3218_,
        v_a_3219_,
    );
    return v___x_3221_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___boxed(
    mut v_preserveBinderNames_3222_: *mut leanh::LeanObject,
    mut v_hygienic_3223_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3224_: *mut leanh::LeanObject,
    mut v_lctx_3225_: *mut leanh::LeanObject,
    mut v_binderName_3226_: *mut leanh::LeanObject,
    mut v_isExplicit_3227_: *mut leanh::LeanObject,
    mut v_x_3228_: *mut leanh::LeanObject,
    mut v_a_3229_: *mut leanh::LeanObject,
    mut v_a_3230_: *mut leanh::LeanObject,
    mut v_a_3231_: *mut leanh::LeanObject,
    mut v_a_3232_: *mut leanh::LeanObject,
    mut v_a_3233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3234_: u8 = 0;
    let mut v_hygienic_boxed_3235_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3236_: u8 = 0;
    let mut v_isExplicit_boxed_3237_: u8 = 0;
    let mut v_res_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3234_ =
        (leanh::lean_unbox(v_preserveBinderNames_3222_) as u8);
    v_hygienic_boxed_3235_ = (leanh::lean_unbox(v_hygienic_3223_) as u8);
    v_useNamesForExplicitOnly_boxed_3236_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_3224_) as u8);
    v_isExplicit_boxed_3237_ = (leanh::lean_unbox(v_isExplicit_3227_) as u8);
    v_res_3238_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(
        v_preserveBinderNames_boxed_3234_,
        v_hygienic_boxed_3235_,
        v_useNamesForExplicitOnly_boxed_3236_,
        v_lctx_3225_,
        v_binderName_3226_,
        v_isExplicit_boxed_3237_,
        v_x_3228_,
        v_a_3229_,
        v_a_3230_,
        v_a_3231_,
        v_a_3232_,
    );
    leanh::lean_dec(v_a_3232_);
    leanh::lean_dec_ref(v_a_3231_);
    leanh::lean_dec(v_a_3230_);
    leanh::lean_dec_ref(v_a_3229_);
    leanh::lean_dec_ref(v_lctx_3225_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
    mut v_mvarId_3239_: *mut leanh::LeanObject,
    mut v_x_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
    mut v___y_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3250_: u8 = 0;
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_a_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3239_,
                    v_x_3240_,
                    v___y_3241_,
                    v___y_3242_,
                    v___y_3243_,
                    v___y_3244_,
                );
                if leanh::lean_obj_tag(v___x_3246_) == 0 {
                    v_a_3247_ = leanh::lean_ctor_get(v___x_3246_, 0);
                    v_isSharedCheck_3254_ = (!leanh::lean_is_exclusive(v___x_3246_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v___x_3249_ = v___x_3246_;
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3247_);
                        leanh::lean_dec(v___x_3246_);
                        v___x_3249_ = leanh::lean_box(0);
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3255_ = leanh::lean_ctor_get(v___x_3246_, 0);
                    v_isSharedCheck_3262_ = (!leanh::lean_is_exclusive(v___x_3246_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3257_ = v___x_3246_;
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3255_);
                        leanh::lean_dec(v___x_3246_);
                        v___x_3257_ = leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3250_ == 0 {
                    v___x_3252_ = v___x_3249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
                    v___x_3252_ = v_reuseFailAlloc_3253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3252_;
            }
            3 => {
                if v_isShared_3258_ == 0 {
                    v___x_3260_ = v___x_3257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
                    v___x_3260_ = v_reuseFailAlloc_3261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg___boxed(
    mut v_mvarId_3263_: *mut leanh::LeanObject,
    mut v_x_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
    mut v___y_3266_: *mut leanh::LeanObject,
    mut v___y_3267_: *mut leanh::LeanObject,
    mut v___y_3268_: *mut leanh::LeanObject,
    mut v___y_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
        v_mvarId_3263_,
        v_x_3264_,
        v___y_3265_,
        v___y_3266_,
        v___y_3267_,
        v___y_3268_,
    );
    leanh::lean_dec(v___y_3268_);
    leanh::lean_dec_ref(v___y_3267_);
    leanh::lean_dec(v___y_3266_);
    leanh::lean_dec_ref(v___y_3265_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(
    mut v_00_u03b1_3271_: *mut leanh::LeanObject,
    mut v_mvarId_3272_: *mut leanh::LeanObject,
    mut v_x_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3279_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
        v_mvarId_3272_,
        v_x_3273_,
        v___y_3274_,
        v___y_3275_,
        v___y_3276_,
        v___y_3277_,
    );
    return v___x_3279_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___boxed(
    mut v_00_u03b1_3280_: *mut leanh::LeanObject,
    mut v_mvarId_3281_: *mut leanh::LeanObject,
    mut v_x_3282_: *mut leanh::LeanObject,
    mut v___y_3283_: *mut leanh::LeanObject,
    mut v___y_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
    mut v___y_3287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3288_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(
        v_00_u03b1_3280_,
        v_mvarId_3281_,
        v_x_3282_,
        v___y_3283_,
        v___y_3284_,
        v___y_3285_,
        v___y_3286_,
    );
    leanh::lean_dec(v___y_3286_);
    leanh::lean_dec_ref(v___y_3285_);
    leanh::lean_dec(v___y_3284_);
    leanh::lean_dec_ref(v___y_3283_);
    return v_res_3288_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(
    mut v_sz_3289_: usize,
    mut v_i_3290_: usize,
    mut v_bs_3291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3292_: u8 = 0;
    let mut v_v_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: usize = 0;
    let mut v___x_3298_: usize = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3292_ = lean_usize_dec_lt(v_i_3290_, v_sz_3289_);
                if v___x_3292_ == 0 {
                    return v_bs_3291_;
                } else {
                    v_v_3293_ = lean_array_uget(v_bs_3291_, v_i_3290_);
                    v___x_3294_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3295_ = lean_array_uset(v_bs_3291_, v_i_3290_, v___x_3294_);
                    v___x_3296_ = l_Lean_Expr_fvarId_x21(v_v_3293_);
                    leanh::lean_dec(v_v_3293_);
                    v___x_3297_ = 1usize;
                    v___x_3298_ = lean_usize_add(v_i_3290_, v___x_3297_);
                    v___x_3299_ = lean_array_uset(v_bs_x27_3295_, v_i_3290_, v___x_3296_);
                    v_i_3290_ = v___x_3298_;
                    v_bs_3291_ = v___x_3299_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1___boxed(
    mut v_sz_3301_: *mut leanh::LeanObject,
    mut v_i_3302_: *mut leanh::LeanObject,
    mut v_bs_3303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3304_: usize = 0;
    let mut v_i_boxed_3305_: usize = 0;
    let mut v_res_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3304_ = leanh::lean_unbox_usize(v_sz_3301_);
    leanh::lean_dec(v_sz_3301_);
    v_i_boxed_3305_ = leanh::lean_unbox_usize(v_i_3302_);
    leanh::lean_dec(v_i_3302_);
    v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_3304_, v_i_boxed_3305_, v_bs_3303_);
    return v_res_3306_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(
    mut v_e_3307_: *mut leanh::LeanObject,
    mut v___y_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut v_unused_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3310_ = l_Lean_Expr_hasMVar(v_e_3307_);
                if v___x_3310_ == 0 {
                    v___x_3311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3311_, 0, v_e_3307_);
                    return v___x_3311_;
                } else {
                    v___x_3312_ = lean_st_ref_get(v___y_3308_);
                    v_mctx_3313_ = leanh::lean_ctor_get(v___x_3312_, 0);
                    leanh::lean_inc_ref(v_mctx_3313_);
                    leanh::lean_dec(v___x_3312_);
                    v___x_3314_ = l_Lean_instantiateMVarsCore(v_mctx_3313_, v_e_3307_);
                    v_fst_3315_ = leanh::lean_ctor_get(v___x_3314_, 0);
                    leanh::lean_inc(v_fst_3315_);
                    v_snd_3316_ = leanh::lean_ctor_get(v___x_3314_, 1);
                    leanh::lean_inc(v_snd_3316_);
                    leanh::lean_dec_ref(v___x_3314_);
                    v___x_3317_ = lean_st_ref_take(v___y_3308_);
                    v_cache_3318_ = leanh::lean_ctor_get(v___x_3317_, 1);
                    v_zetaDeltaFVarIds_3319_ = leanh::lean_ctor_get(v___x_3317_, 2);
                    v_postponed_3320_ = leanh::lean_ctor_get(v___x_3317_, 3);
                    v_diag_3321_ = leanh::lean_ctor_get(v___x_3317_, 4);
                    v_isSharedCheck_3330_ = (!leanh::lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v_unused_3331_ = leanh::lean_ctor_get(v___x_3317_, 0);
                        leanh::lean_dec(v_unused_3331_);
                        v___x_3323_ = v___x_3317_;
                        v_isShared_3324_ = v_isSharedCheck_3330_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3321_);
                        leanh::lean_inc(v_postponed_3320_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3319_);
                        leanh::lean_inc(v_cache_3318_);
                        leanh::lean_dec(v___x_3317_);
                        v___x_3323_ = leanh::lean_box(0);
                        v_isShared_3324_ = v_isSharedCheck_3330_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3324_ == 0 {
                    leanh::lean_ctor_set(v___x_3323_, 0, v_snd_3316_);
                    v___x_3326_ = v___x_3323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_snd_3316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_cache_3318_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3329_,
                        2,
                        v_zetaDeltaFVarIds_3319_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_postponed_3320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_diag_3321_);
                    v___x_3326_ = v_reuseFailAlloc_3329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3327_ = lean_st_ref_set(v___y_3308_, v___x_3326_);
                v___x_3328_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3328_, 0, v_fst_3315_);
                return v___x_3328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(
    mut v_e_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_3332_, v___y_3333_);
    leanh::lean_dec(v___y_3333_);
    return v_res_3335_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(
    mut v___y_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v_r_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_unused_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3338_ = lean_st_ref_get(v___y_3336_);
                v_ngen_3339_ = leanh::lean_ctor_get(v___x_3338_, 2);
                leanh::lean_inc_ref(v_ngen_3339_);
                leanh::lean_dec(v___x_3338_);
                v_namePrefix_3340_ = leanh::lean_ctor_get(v_ngen_3339_, 0);
                v_idx_3341_ = leanh::lean_ctor_get(v_ngen_3339_, 1);
                v_isSharedCheck_3370_ = (!leanh::lean_is_exclusive(v_ngen_3339_)) as u8;
                if v_isSharedCheck_3370_ == 0 {
                    v___x_3343_ = v_ngen_3339_;
                    v_isShared_3344_ = v_isSharedCheck_3370_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_3341_);
                    leanh::lean_inc(v_namePrefix_3340_);
                    leanh::lean_dec(v_ngen_3339_);
                    v___x_3343_ = leanh::lean_box(0);
                    v_isShared_3344_ = v_isSharedCheck_3370_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3345_ = lean_st_ref_take(v___y_3336_);
                v_env_3346_ = leanh::lean_ctor_get(v___x_3345_, 0);
                v_nextMacroScope_3347_ = leanh::lean_ctor_get(v___x_3345_, 1);
                v_auxDeclNGen_3348_ = leanh::lean_ctor_get(v___x_3345_, 3);
                v_traceState_3349_ = leanh::lean_ctor_get(v___x_3345_, 4);
                v_cache_3350_ = leanh::lean_ctor_get(v___x_3345_, 5);
                v_messages_3351_ = leanh::lean_ctor_get(v___x_3345_, 6);
                v_infoState_3352_ = leanh::lean_ctor_get(v___x_3345_, 7);
                v_snapshotTasks_3353_ = leanh::lean_ctor_get(v___x_3345_, 8);
                v_isSharedCheck_3368_ = (!leanh::lean_is_exclusive(v___x_3345_)) as u8;
                if v_isSharedCheck_3368_ == 0 {
                    v_unused_3369_ = leanh::lean_ctor_get(v___x_3345_, 2);
                    leanh::lean_dec(v_unused_3369_);
                    v___x_3355_ = v___x_3345_;
                    v_isShared_3356_ = v_isSharedCheck_3368_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3353_);
                    leanh::lean_inc(v_infoState_3352_);
                    leanh::lean_inc(v_messages_3351_);
                    leanh::lean_inc(v_cache_3350_);
                    leanh::lean_inc(v_traceState_3349_);
                    leanh::lean_inc(v_auxDeclNGen_3348_);
                    leanh::lean_inc(v_nextMacroScope_3347_);
                    leanh::lean_inc(v_env_3346_);
                    leanh::lean_dec(v___x_3345_);
                    v___x_3355_ = leanh::lean_box(0);
                    v_isShared_3356_ = v_isSharedCheck_3368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_3341_);
                leanh::lean_inc(v_namePrefix_3340_);
                v_r_3357_ = l_Lean_Name_num___override(v_namePrefix_3340_, v_idx_3341_);
                v___x_3358_ = leanh::lean_unsigned_to_nat(1);
                v___x_3359_ = lean_nat_add(v_idx_3341_, v___x_3358_);
                leanh::lean_dec(v_idx_3341_);
                if v_isShared_3344_ == 0 {
                    leanh::lean_ctor_set(v___x_3343_, 1, v___x_3359_);
                    v___x_3361_ = v___x_3343_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_namePrefix_3340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 1, v___x_3359_);
                    v___x_3361_ = v_reuseFailAlloc_3367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3356_ == 0 {
                    leanh::lean_ctor_set(v___x_3355_, 2, v___x_3361_);
                    v___x_3363_ = v___x_3355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3366_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_env_3346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_nextMacroScope_3347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 2, v___x_3361_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 3, v_auxDeclNGen_3348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 4, v_traceState_3349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 5, v_cache_3350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 6, v_messages_3351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 7, v_infoState_3352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 8, v_snapshotTasks_3353_);
                    v___x_3363_ = v_reuseFailAlloc_3366_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3364_ = lean_st_ref_set(v___y_3336_, v___x_3363_);
                v___x_3365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3365_, 0, v_r_3357_);
                return v___x_3365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(
    mut v___y_3371_: *mut leanh::LeanObject,
    mut v___y_3372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_3371_);
    leanh::lean_dec(v___y_3371_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(
    mut v___y_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3379_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_3377_);
                v_a_3380_ = leanh::lean_ctor_get(v___x_3379_, 0);
                v_isSharedCheck_3387_ = (!leanh::lean_is_exclusive(v___x_3379_)) as u8;
                if v_isSharedCheck_3387_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    v_isShared_3383_ = v_isSharedCheck_3387_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3380_);
                    leanh::lean_dec(v___x_3379_);
                    v___x_3382_ = leanh::lean_box(0);
                    v_isShared_3383_ = v_isSharedCheck_3387_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3383_ == 0 {
                    v___x_3385_ = v___x_3382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
                    v___x_3385_ = v_reuseFailAlloc_3386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3___boxed(
    mut v___y_3388_: *mut leanh::LeanObject,
    mut v___y_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    leanh::lean_dec(v___y_3391_);
    leanh::lean_dec_ref(v___y_3390_);
    leanh::lean_dec(v___y_3389_);
    leanh::lean_dec_ref(v___y_3388_);
    return v_res_3393_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(
    mut v_fvars_3394_: *mut leanh::LeanObject,
    mut v_j_3395_: *mut leanh::LeanObject,
    mut v_x_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3406_: u8 = 0;
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut v_a_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(
                    leanh::lean_box(0),
                    v_fvars_3394_,
                    v_j_3395_,
                    v_x_3396_,
                    v___y_3397_,
                    v___y_3398_,
                    v___y_3399_,
                    v___y_3400_,
                );
                if leanh::lean_obj_tag(v___x_3402_) == 0 {
                    v_a_3403_ = leanh::lean_ctor_get(v___x_3402_, 0);
                    v_isSharedCheck_3410_ = (!leanh::lean_is_exclusive(v___x_3402_)) as u8;
                    if v_isSharedCheck_3410_ == 0 {
                        v___x_3405_ = v___x_3402_;
                        v_isShared_3406_ = v_isSharedCheck_3410_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3403_);
                        leanh::lean_dec(v___x_3402_);
                        v___x_3405_ = leanh::lean_box(0);
                        v_isShared_3406_ = v_isSharedCheck_3410_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3411_ = leanh::lean_ctor_get(v___x_3402_, 0);
                    v_isSharedCheck_3418_ = (!leanh::lean_is_exclusive(v___x_3402_)) as u8;
                    if v_isSharedCheck_3418_ == 0 {
                        v___x_3413_ = v___x_3402_;
                        v_isShared_3414_ = v_isSharedCheck_3418_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3411_);
                        leanh::lean_dec(v___x_3402_);
                        v___x_3413_ = leanh::lean_box(0);
                        v_isShared_3414_ = v_isSharedCheck_3418_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3406_ == 0 {
                    v___x_3408_ = v___x_3405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
                    v___x_3408_ = v_reuseFailAlloc_3409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3408_;
            }
            3 => {
                if v_isShared_3414_ == 0 {
                    v___x_3416_ = v___x_3413_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
                    v___x_3416_ = v_reuseFailAlloc_3417_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_fvars_3419_: *mut leanh::LeanObject,
    mut v_j_3420_: *mut leanh::LeanObject,
    mut v_x_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_3419_, v_j_3420_, v_x_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
    leanh::lean_dec(v___y_3425_);
    leanh::lean_dec_ref(v___y_3424_);
    leanh::lean_dec(v___y_3423_);
    leanh::lean_dec_ref(v___y_3422_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(
    mut v_fvars_3428_: *mut leanh::LeanObject,
    mut v_j_3429_: *mut leanh::LeanObject,
    mut v_x_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
    mut v___y_3432_: *mut leanh::LeanObject,
    mut v___y_3433_: *mut leanh::LeanObject,
    mut v___y_3434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_a_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3436_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_3428_, v_j_3429_, v_x_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
                if leanh::lean_obj_tag(v___x_3436_) == 0 {
                    v_a_3437_ = leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3444_ = (!leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3444_ == 0 {
                        v___x_3439_ = v___x_3436_;
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3437_);
                        leanh::lean_dec(v___x_3436_);
                        v___x_3439_ = leanh::lean_box(0);
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3445_ = leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3452_ = (!leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3452_ == 0 {
                        v___x_3447_ = v___x_3436_;
                        v_isShared_3448_ = v_isSharedCheck_3452_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3445_);
                        leanh::lean_dec(v___x_3436_);
                        v___x_3447_ = leanh::lean_box(0);
                        v_isShared_3448_ = v_isSharedCheck_3452_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3440_ == 0 {
                    v___x_3442_ = v___x_3439_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3442_;
            }
            3 => {
                if v_isShared_3448_ == 0 {
                    v___x_3450_ = v___x_3447_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
                    v___x_3450_ = v_reuseFailAlloc_3451_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg___boxed(
    mut v_fvars_3453_: *mut leanh::LeanObject,
    mut v_j_3454_: *mut leanh::LeanObject,
    mut v_x_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_3453_, v_j_3454_, v_x_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
    leanh::lean_dec(v___y_3459_);
    leanh::lean_dec_ref(v___y_3458_);
    leanh::lean_dec(v___y_3457_);
    leanh::lean_dec_ref(v___y_3456_);
    return v_res_3461_;
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(
    mut v_00_u03b1_3462_: *mut leanh::LeanObject,
    mut v_fvars_3463_: *mut leanh::LeanObject,
    mut v_j_3464_: *mut leanh::LeanObject,
    mut v_x_3465_: *mut leanh::LeanObject,
    mut v___y_3466_: *mut leanh::LeanObject,
    mut v___y_3467_: *mut leanh::LeanObject,
    mut v___y_3468_: *mut leanh::LeanObject,
    mut v___y_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_3463_, v_j_3464_, v_x_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
    return v___x_3471_;
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(
    mut v_00_u03b1_3472_: *mut leanh::LeanObject,
    mut v_fvars_3473_: *mut leanh::LeanObject,
    mut v_j_3474_: *mut leanh::LeanObject,
    mut v_x_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_3472_, v_fvars_3473_, v_j_3474_, v_x_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
    leanh::lean_dec(v___y_3479_);
    leanh::lean_dec_ref(v___y_3478_);
    leanh::lean_dec(v___y_3477_);
    leanh::lean_dec_ref(v___y_3476_);
    return v_res_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(
    mut v_x_3482_: *mut leanh::LeanObject,
    mut v_x_3483_: *mut leanh::LeanObject,
    mut v_x_3484_: *mut leanh::LeanObject,
    mut v_x_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3486_ = leanh::lean_ctor_get(v_x_3482_, 0);
                v_vs_3487_ = leanh::lean_ctor_get(v_x_3482_, 1);
                v_isSharedCheck_3511_ = (!leanh::lean_is_exclusive(v_x_3482_)) as u8;
                if v_isSharedCheck_3511_ == 0 {
                    v___x_3489_ = v_x_3482_;
                    v_isShared_3490_ = v_isSharedCheck_3511_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3487_);
                    leanh::lean_inc(v_ks_3486_);
                    leanh::lean_dec(v_x_3482_);
                    v___x_3489_ = leanh::lean_box(0);
                    v_isShared_3490_ = v_isSharedCheck_3511_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3491_ = lean_array_get_size(v_ks_3486_);
                v___x_3492_ = lean_nat_dec_lt(v_x_3483_, v___x_3491_);
                if v___x_3492_ == 0 {
                    leanh::lean_dec(v_x_3483_);
                    v___x_3493_ = lean_array_push(v_ks_3486_, v_x_3484_);
                    v___x_3494_ = lean_array_push(v_vs_3487_, v_x_3485_);
                    if v_isShared_3490_ == 0 {
                        leanh::lean_ctor_set(v___x_3489_, 1, v___x_3494_);
                        leanh::lean_ctor_set(v___x_3489_, 0, v___x_3493_);
                        v___x_3496_ = v___x_3489_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3497_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3493_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3494_);
                        v___x_3496_ = v_reuseFailAlloc_3497_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3498_ = lean_array_fget_borrowed(v_ks_3486_, v_x_3483_);
                    v___x_3499_ = l_Lean_instBEqMVarId_beq(v_x_3484_, v_k_x27_3498_);
                    if v___x_3499_ == 0 {
                        if v_isShared_3490_ == 0 {
                            v___x_3501_ = v___x_3489_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3505_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_ks_3486_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_vs_3487_);
                            v___x_3501_ = v_reuseFailAlloc_3505_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3506_ = lean_array_fset(v_ks_3486_, v_x_3483_, v_x_3484_);
                        v___x_3507_ = lean_array_fset(v_vs_3487_, v_x_3483_, v_x_3485_);
                        leanh::lean_dec(v_x_3483_);
                        if v_isShared_3490_ == 0 {
                            leanh::lean_ctor_set(v___x_3489_, 1, v___x_3507_);
                            leanh::lean_ctor_set(v___x_3489_, 0, v___x_3506_);
                            v___x_3509_ = v___x_3489_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3510_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3506_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3507_);
                            v___x_3509_ = v_reuseFailAlloc_3510_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3496_;
            }
            3 => {
                v___x_3502_ = leanh::lean_unsigned_to_nat(1);
                v___x_3503_ = lean_nat_add(v_x_3483_, v___x_3502_);
                leanh::lean_dec(v_x_3483_);
                v_x_3482_ = v___x_3501_;
                v_x_3483_ = v___x_3503_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(
    mut v_n_3512_: *mut leanh::LeanObject,
    mut v_k_3513_: *mut leanh::LeanObject,
    mut v_v_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = leanh::lean_unsigned_to_nat(0);
    v___x_3516_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_n_3512_, v___x_3515_, v_k_3513_, v_v_3514_);
    return v___x_3516_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: usize = 0;
    let mut v___x_3519_: usize = 0;
    v___x_3517_ = 5usize;
    v___x_3518_ = 1usize;
    v___x_3519_ = lean_usize_shift_left(v___x_3518_, v___x_3517_);
    return v___x_3519_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_3520_: usize = 0;
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: usize = 0;
    v___x_3520_ = 1usize;
    v___x_3521_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
    v___x_3522_ = lean_usize_sub(v___x_3521_, v___x_3520_);
    return v___x_3522_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3523_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_x_3524_: *mut leanh::LeanObject,
    mut v_x_3525_: usize,
    mut v_x_3526_: usize,
    mut v_x_3527_: *mut leanh::LeanObject,
    mut v_x_3528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: usize = 0;
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: usize = 0;
    let mut v_j_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v_v_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_node_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3565_: usize = 0;
    let mut v___x_3566_: usize = 0;
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3573_: u8 = 0;
    let mut v_unused_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: u8 = 0;
    let mut v_ks_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: usize = 0;
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v_reuseFailAlloc_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3524_) == 0 {
                    v_es_3529_ = leanh::lean_ctor_get(v_x_3524_, 0);
                    v___x_3530_ = 5usize;
                    v___x_3531_ = 1usize;
                    v___x_3532_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1);
                    v___x_3533_ = lean_usize_land(v_x_3525_, v___x_3532_);
                    v_j_3534_ = lean_usize_to_nat(v___x_3533_);
                    v___x_3535_ = lean_array_get_size(v_es_3529_);
                    v___x_3536_ = lean_nat_dec_lt(v_j_3534_, v___x_3535_);
                    if v___x_3536_ == 0 {
                        leanh::lean_dec(v_j_3534_);
                        leanh::lean_dec(v_x_3528_);
                        leanh::lean_dec(v_x_3527_);
                        return v_x_3524_;
                    } else {
                        leanh::lean_inc_ref(v_es_3529_);
                        v_isSharedCheck_3573_ = (!leanh::lean_is_exclusive(v_x_3524_)) as u8;
                        if v_isSharedCheck_3573_ == 0 {
                            v_unused_3574_ = leanh::lean_ctor_get(v_x_3524_, 0);
                            leanh::lean_dec(v_unused_3574_);
                            v___x_3538_ = v_x_3524_;
                            v_isShared_3539_ = v_isSharedCheck_3573_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3524_);
                            v___x_3538_ = leanh::lean_box(0);
                            v_isShared_3539_ = v_isSharedCheck_3573_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3575_ = leanh::lean_ctor_get(v_x_3524_, 0);
                    v_vs_3576_ = leanh::lean_ctor_get(v_x_3524_, 1);
                    v_isSharedCheck_3596_ = (!leanh::lean_is_exclusive(v_x_3524_)) as u8;
                    if v_isSharedCheck_3596_ == 0 {
                        v___x_3578_ = v_x_3524_;
                        v_isShared_3579_ = v_isSharedCheck_3596_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3576_);
                        leanh::lean_inc(v_ks_3575_);
                        leanh::lean_dec(v_x_3524_);
                        v___x_3578_ = leanh::lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3596_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3540_ = lean_array_fget(v_es_3529_, v_j_3534_);
                v___x_3541_ = leanh::lean_box(0);
                v_xs_x27_3542_ = lean_array_fset(v_es_3529_, v_j_3534_, v___x_3541_);
                match leanh::lean_obj_tag(v_v_3540_) {
                    0 => {
                        v_key_3549_ = leanh::lean_ctor_get(v_v_3540_, 0);
                        v_val_3550_ = leanh::lean_ctor_get(v_v_3540_, 1);
                        v_isSharedCheck_3560_ = (!leanh::lean_is_exclusive(v_v_3540_)) as u8;
                        if v_isSharedCheck_3560_ == 0 {
                            v___x_3552_ = v_v_3540_;
                            v_isShared_3553_ = v_isSharedCheck_3560_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3550_);
                            leanh::lean_inc(v_key_3549_);
                            leanh::lean_dec(v_v_3540_);
                            v___x_3552_ = leanh::lean_box(0);
                            v_isShared_3553_ = v_isSharedCheck_3560_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3561_ = leanh::lean_ctor_get(v_v_3540_, 0);
                        v_isSharedCheck_3571_ = (!leanh::lean_is_exclusive(v_v_3540_)) as u8;
                        if v_isSharedCheck_3571_ == 0 {
                            v___x_3563_ = v_v_3540_;
                            v_isShared_3564_ = v_isSharedCheck_3571_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3561_);
                            leanh::lean_dec(v_v_3540_);
                            v___x_3563_ = leanh::lean_box(0);
                            v_isShared_3564_ = v_isSharedCheck_3571_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3572_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3572_, 0, v_x_3527_);
                        leanh::lean_ctor_set(v___x_3572_, 1, v_x_3528_);
                        v___y_3544_ = v___x_3572_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3545_ = lean_array_fset(v_xs_x27_3542_, v_j_3534_, v___y_3544_);
                leanh::lean_dec(v_j_3534_);
                if v_isShared_3539_ == 0 {
                    leanh::lean_ctor_set(v___x_3538_, 0, v___x_3545_);
                    v___x_3547_ = v___x_3538_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
                    v___x_3547_ = v_reuseFailAlloc_3548_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3547_;
            }
            4 => {
                v___x_3554_ = l_Lean_instBEqMVarId_beq(v_x_3527_, v_key_3549_);
                if v___x_3554_ == 0 {
                    leanh::lean_del_object(v___x_3552_);
                    v___x_3555_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3549_,
                        v_val_3550_,
                        v_x_3527_,
                        v_x_3528_,
                    );
                    v___x_3556_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3556_, 0, v___x_3555_);
                    v___y_3544_ = v___x_3556_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3550_);
                    leanh::lean_dec(v_key_3549_);
                    if v_isShared_3553_ == 0 {
                        leanh::lean_ctor_set(v___x_3552_, 1, v_x_3528_);
                        leanh::lean_ctor_set(v___x_3552_, 0, v_x_3527_);
                        v___x_3558_ = v___x_3552_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3559_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_x_3527_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_x_3528_);
                        v___x_3558_ = v_reuseFailAlloc_3559_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3544_ = v___x_3558_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3565_ = lean_usize_shift_right(v_x_3525_, v___x_3530_);
                v___x_3566_ = lean_usize_add(v_x_3526_, v___x_3531_);
                v___x_3567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_node_3561_, v___x_3565_, v___x_3566_, v_x_3527_, v_x_3528_);
                if v_isShared_3564_ == 0 {
                    leanh::lean_ctor_set(v___x_3563_, 0, v___x_3567_);
                    v___x_3569_ = v___x_3563_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
                    v___x_3569_ = v_reuseFailAlloc_3570_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3544_ = v___x_3569_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3579_ == 0 {
                    v___x_3581_ = v___x_3578_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3595_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_ks_3575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_vs_3576_);
                    v___x_3581_ = v_reuseFailAlloc_3595_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3582_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v___x_3581_, v_x_3527_, v_x_3528_);
                v___x_3590_ = 7usize;
                v___x_3591_ = lean_usize_dec_le(v___x_3590_, v_x_3526_);
                if v___x_3591_ == 0 {
                    v___x_3592_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3582_);
                    v___x_3593_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3594_ = lean_nat_dec_lt(v___x_3592_, v___x_3593_);
                    leanh::lean_dec(v___x_3592_);
                    v___y_3584_ = v___x_3594_;
                    state = 10;
                    continue;
                } else {
                    v___y_3584_ = v___x_3591_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3584_ == 0 {
                    v_ks_3585_ = leanh::lean_ctor_get(v_newNode_3582_, 0);
                    leanh::lean_inc_ref(v_ks_3585_);
                    v_vs_3586_ = leanh::lean_ctor_get(v_newNode_3582_, 1);
                    leanh::lean_inc_ref(v_vs_3586_);
                    leanh::lean_dec_ref(v_newNode_3582_);
                    v___x_3587_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2);
                    v___x_3589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_3526_, v_ks_3585_, v_vs_3586_, v___x_3587_, v___x_3588_);
                    leanh::lean_dec_ref(v_vs_3586_);
                    leanh::lean_dec_ref(v_ks_3585_);
                    return v___x_3589_;
                } else {
                    return v_newNode_3582_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_depth_3597_: usize,
    mut v_keys_3598_: *mut leanh::LeanObject,
    mut v_vals_3599_: *mut leanh::LeanObject,
    mut v_i_3600_: *mut leanh::LeanObject,
    mut v_entries_3601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v_k_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: u64 = 0;
    let mut v_h_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: usize = 0;
    let mut v___x_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v_h_3613_: usize = 0;
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3602_ = lean_array_get_size(v_keys_3598_);
                v___x_3603_ = lean_nat_dec_lt(v_i_3600_, v___x_3602_);
                if v___x_3603_ == 0 {
                    leanh::lean_dec(v_i_3600_);
                    return v_entries_3601_;
                } else {
                    v_k_3604_ = lean_array_fget_borrowed(v_keys_3598_, v_i_3600_);
                    v_v_3605_ = lean_array_fget_borrowed(v_vals_3599_, v_i_3600_);
                    v___x_3606_ = l_Lean_instHashableMVarId_hash(v_k_3604_);
                    v_h_3607_ = lean_uint64_to_usize(v___x_3606_);
                    v___x_3608_ = 5usize;
                    v___x_3609_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3610_ = 1usize;
                    v___x_3611_ = lean_usize_sub(v_depth_3597_, v___x_3610_);
                    v___x_3612_ = lean_usize_mul(v___x_3608_, v___x_3611_);
                    v_h_3613_ = lean_usize_shift_right(v_h_3607_, v___x_3612_);
                    v___x_3614_ = lean_nat_add(v_i_3600_, v___x_3609_);
                    leanh::lean_dec(v_i_3600_);
                    leanh::lean_inc(v_v_3605_);
                    leanh::lean_inc(v_k_3604_);
                    v___x_3615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_entries_3601_, v_h_3613_, v_depth_3597_, v_k_3604_, v_v_3605_);
                    v_i_3600_ = v___x_3614_;
                    v_entries_3601_ = v___x_3615_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_depth_3617_: *mut leanh::LeanObject,
    mut v_keys_3618_: *mut leanh::LeanObject,
    mut v_vals_3619_: *mut leanh::LeanObject,
    mut v_i_3620_: *mut leanh::LeanObject,
    mut v_entries_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3622_: usize = 0;
    let mut v_res_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3622_ = leanh::lean_unbox_usize(v_depth_3617_);
    leanh::lean_dec(v_depth_3617_);
    v_res_3623_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_3622_, v_keys_3618_, v_vals_3619_, v_i_3620_, v_entries_3621_);
    leanh::lean_dec_ref(v_vals_3619_);
    leanh::lean_dec_ref(v_keys_3618_);
    return v_res_3623_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_x_3624_: *mut leanh::LeanObject,
    mut v_x_3625_: *mut leanh::LeanObject,
    mut v_x_3626_: *mut leanh::LeanObject,
    mut v_x_3627_: *mut leanh::LeanObject,
    mut v_x_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3906__boxed_3629_: usize = 0;
    let mut v_x_3907__boxed_3630_: usize = 0;
    let mut v_res_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3906__boxed_3629_ = leanh::lean_unbox_usize(v_x_3625_);
    leanh::lean_dec(v_x_3625_);
    v_x_3907__boxed_3630_ = leanh::lean_unbox_usize(v_x_3626_);
    leanh::lean_dec(v_x_3626_);
    v_res_3631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_3624_, v_x_3906__boxed_3629_, v_x_3907__boxed_3630_, v_x_3627_, v_x_3628_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(
    mut v_x_3632_: *mut leanh::LeanObject,
    mut v_x_3633_: *mut leanh::LeanObject,
    mut v_x_3634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3635_: u64 = 0;
    let mut v___x_3636_: usize = 0;
    let mut v___x_3637_: usize = 0;
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3635_ = l_Lean_instHashableMVarId_hash(v_x_3633_);
    v___x_3636_ = lean_uint64_to_usize(v___x_3635_);
    v___x_3637_ = 1usize;
    v___x_3638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_3632_, v___x_3636_, v___x_3637_, v_x_3633_, v_x_3634_);
    return v___x_3638_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(
    mut v_mvarId_3639_: *mut leanh::LeanObject,
    mut v_val_3640_: *mut leanh::LeanObject,
    mut v___y_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v_depth_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3643_ = lean_st_ref_take(v___y_3641_);
                v_mctx_3644_ = leanh::lean_ctor_get(v___x_3643_, 0);
                v_cache_3645_ = leanh::lean_ctor_get(v___x_3643_, 1);
                v_zetaDeltaFVarIds_3646_ = leanh::lean_ctor_get(v___x_3643_, 2);
                v_postponed_3647_ = leanh::lean_ctor_get(v___x_3643_, 3);
                v_diag_3648_ = leanh::lean_ctor_get(v___x_3643_, 4);
                v_isSharedCheck_3676_ = (!leanh::lean_is_exclusive(v___x_3643_)) as u8;
                if v_isSharedCheck_3676_ == 0 {
                    v___x_3650_ = v___x_3643_;
                    v_isShared_3651_ = v_isSharedCheck_3676_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3648_);
                    leanh::lean_inc(v_postponed_3647_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3646_);
                    leanh::lean_inc(v_cache_3645_);
                    leanh::lean_inc(v_mctx_3644_);
                    leanh::lean_dec(v___x_3643_);
                    v___x_3650_ = leanh::lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3676_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3652_ = leanh::lean_ctor_get(v_mctx_3644_, 0);
                v_levelAssignDepth_3653_ = leanh::lean_ctor_get(v_mctx_3644_, 1);
                v_lmvarCounter_3654_ = leanh::lean_ctor_get(v_mctx_3644_, 2);
                v_mvarCounter_3655_ = leanh::lean_ctor_get(v_mctx_3644_, 3);
                v_lDecls_3656_ = leanh::lean_ctor_get(v_mctx_3644_, 4);
                v_decls_3657_ = leanh::lean_ctor_get(v_mctx_3644_, 5);
                v_userNames_3658_ = leanh::lean_ctor_get(v_mctx_3644_, 6);
                v_lAssignment_3659_ = leanh::lean_ctor_get(v_mctx_3644_, 7);
                v_eAssignment_3660_ = leanh::lean_ctor_get(v_mctx_3644_, 8);
                v_dAssignment_3661_ = leanh::lean_ctor_get(v_mctx_3644_, 9);
                v_isSharedCheck_3675_ = (!leanh::lean_is_exclusive(v_mctx_3644_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v___x_3663_ = v_mctx_3644_;
                    v_isShared_3664_ = v_isSharedCheck_3675_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3661_);
                    leanh::lean_inc(v_eAssignment_3660_);
                    leanh::lean_inc(v_lAssignment_3659_);
                    leanh::lean_inc(v_userNames_3658_);
                    leanh::lean_inc(v_decls_3657_);
                    leanh::lean_inc(v_lDecls_3656_);
                    leanh::lean_inc(v_mvarCounter_3655_);
                    leanh::lean_inc(v_lmvarCounter_3654_);
                    leanh::lean_inc(v_levelAssignDepth_3653_);
                    leanh::lean_inc(v_depth_3652_);
                    leanh::lean_dec(v_mctx_3644_);
                    v___x_3663_ = leanh::lean_box(0);
                    v_isShared_3664_ = v_isSharedCheck_3675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3665_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_3660_, v_mvarId_3639_, v_val_3640_);
                if v_isShared_3664_ == 0 {
                    leanh::lean_ctor_set(v___x_3663_, 8, v___x_3665_);
                    v___x_3667_ = v___x_3663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_depth_3652_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3674_,
                        1,
                        v_levelAssignDepth_3653_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_lmvarCounter_3654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_mvarCounter_3655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_lDecls_3656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_decls_3657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_userNames_3658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_lAssignment_3659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 8, v___x_3665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_dAssignment_3661_);
                    v___x_3667_ = v_reuseFailAlloc_3674_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3651_ == 0 {
                    leanh::lean_ctor_set(v___x_3650_, 0, v___x_3667_);
                    v___x_3669_ = v___x_3650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_cache_3645_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3673_,
                        2,
                        v_zetaDeltaFVarIds_3646_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_postponed_3647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_diag_3648_);
                    v___x_3669_ = v_reuseFailAlloc_3673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3670_ = lean_st_ref_set(v___y_3641_, v___x_3669_);
                v___x_3671_ = leanh::lean_box(0);
                v___x_3672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3672_, 0, v___x_3671_);
                return v___x_3672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(
    mut v_mvarId_3677_: *mut leanh::LeanObject,
    mut v_val_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_3677_, v_val_3678_, v___y_3679_);
    leanh::lean_dec(v___y_3679_);
    return v_res_3681_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(
    mut v_mvarId_3682_: *mut leanh::LeanObject,
    mut v_type_3683_: *mut leanh::LeanObject,
    mut v_fvars_3684_: *mut leanh::LeanObject,
    mut v_isZero_3685_: u8,
    mut v___y_3686_: *mut leanh::LeanObject,
    mut v___y_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_unused_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v_a_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3722_: u8 = 0;
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3726_: u8 = 0;
    let mut v_a_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3734_: u8 = 0;
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3682_);
                v___x_3691_ = l_Lean_MVarId_getTag(
                    v_mvarId_3682_,
                    v___y_3686_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                );
                if leanh::lean_obj_tag(v___x_3691_) == 0 {
                    v_a_3692_ = leanh::lean_ctor_get(v___x_3691_, 0);
                    leanh::lean_inc(v_a_3692_);
                    leanh::lean_dec_ref_known(v___x_3691_, 1);
                    v___x_3693_ = l_Lean_Expr_headBeta(v_type_3683_);
                    v___x_3694_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_3693_,
                        v_a_3692_,
                        v___y_3686_,
                        v___y_3687_,
                        v___y_3688_,
                        v___y_3689_,
                    );
                    if leanh::lean_obj_tag(v___x_3694_) == 0 {
                        v_a_3695_ = leanh::lean_ctor_get(v___x_3694_, 0);
                        leanh::lean_inc_n(v_a_3695_, 2);
                        leanh::lean_dec_ref_known(v___x_3694_, 1);
                        v___x_3696_ = 0;
                        v___x_3697_ = 1;
                        v___x_3698_ = l_Lean_Meta_mkLambdaFVars(
                            v_fvars_3684_,
                            v_a_3695_,
                            v___x_3696_,
                            v_isZero_3685_,
                            v___x_3696_,
                            v_isZero_3685_,
                            v___x_3697_,
                            v___y_3686_,
                            v___y_3687_,
                            v___y_3688_,
                            v___y_3689_,
                        );
                        if leanh::lean_obj_tag(v___x_3698_) == 0 {
                            v_a_3699_ = leanh::lean_ctor_get(v___x_3698_, 0);
                            leanh::lean_inc(v_a_3699_);
                            leanh::lean_dec_ref_known(v___x_3698_, 1);
                            v___x_3700_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_3682_, v_a_3699_, v___y_3687_);
                            if leanh::lean_obj_tag(v___x_3700_) == 0 {
                                v_isSharedCheck_3709_ =
                                    (!leanh::lean_is_exclusive(v___x_3700_)) as u8;
                                if v_isSharedCheck_3709_ == 0 {
                                    v_unused_3710_ = leanh::lean_ctor_get(v___x_3700_, 0);
                                    leanh::lean_dec(v_unused_3710_);
                                    v___x_3702_ = v___x_3700_;
                                    v_isShared_3703_ = v_isSharedCheck_3709_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_3700_);
                                    v___x_3702_ = leanh::lean_box(0);
                                    v_isShared_3703_ = v_isSharedCheck_3709_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_3695_);
                                leanh::lean_dec_ref(v_fvars_3684_);
                                v_a_3711_ = leanh::lean_ctor_get(v___x_3700_, 0);
                                v_isSharedCheck_3718_ =
                                    (!leanh::lean_is_exclusive(v___x_3700_)) as u8;
                                if v_isSharedCheck_3718_ == 0 {
                                    v___x_3713_ = v___x_3700_;
                                    v_isShared_3714_ = v_isSharedCheck_3718_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3711_);
                                    leanh::lean_dec(v___x_3700_);
                                    v___x_3713_ = leanh::lean_box(0);
                                    v_isShared_3714_ = v_isSharedCheck_3718_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_3695_);
                            leanh::lean_dec_ref(v_fvars_3684_);
                            leanh::lean_dec(v_mvarId_3682_);
                            v_a_3719_ = leanh::lean_ctor_get(v___x_3698_, 0);
                            v_isSharedCheck_3726_ =
                                (!leanh::lean_is_exclusive(v___x_3698_)) as u8;
                            if v_isSharedCheck_3726_ == 0 {
                                v___x_3721_ = v___x_3698_;
                                v_isShared_3722_ = v_isSharedCheck_3726_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3719_);
                                leanh::lean_dec(v___x_3698_);
                                v___x_3721_ = leanh::lean_box(0);
                                v_isShared_3722_ = v_isSharedCheck_3726_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_fvars_3684_);
                        leanh::lean_dec(v_mvarId_3682_);
                        v_a_3727_ = leanh::lean_ctor_get(v___x_3694_, 0);
                        v_isSharedCheck_3734_ =
                            (!leanh::lean_is_exclusive(v___x_3694_)) as u8;
                        if v_isSharedCheck_3734_ == 0 {
                            v___x_3729_ = v___x_3694_;
                            v_isShared_3730_ = v_isSharedCheck_3734_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3727_);
                            leanh::lean_dec(v___x_3694_);
                            v___x_3729_ = leanh::lean_box(0);
                            v_isShared_3730_ = v_isSharedCheck_3734_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fvars_3684_);
                    leanh::lean_dec_ref(v_type_3683_);
                    leanh::lean_dec(v_mvarId_3682_);
                    v_a_3735_ = leanh::lean_ctor_get(v___x_3691_, 0);
                    v_isSharedCheck_3742_ = (!leanh::lean_is_exclusive(v___x_3691_)) as u8;
                    if v_isSharedCheck_3742_ == 0 {
                        v___x_3737_ = v___x_3691_;
                        v_isShared_3738_ = v_isSharedCheck_3742_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3735_);
                        leanh::lean_dec(v___x_3691_);
                        v___x_3737_ = leanh::lean_box(0);
                        v_isShared_3738_ = v_isSharedCheck_3742_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3704_ = l_Lean_Expr_mvarId_x21(v_a_3695_);
                leanh::lean_dec(v_a_3695_);
                v___x_3705_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3705_, 0, v_fvars_3684_);
                leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
                if v_isShared_3703_ == 0 {
                    leanh::lean_ctor_set(v___x_3702_, 0, v___x_3705_);
                    v___x_3707_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
                    v___x_3707_ = v_reuseFailAlloc_3708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3707_;
            }
            3 => {
                if v_isShared_3714_ == 0 {
                    v___x_3716_ = v___x_3713_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3716_;
            }
            5 => {
                if v_isShared_3722_ == 0 {
                    v___x_3724_ = v___x_3721_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3725_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
                    v___x_3724_ = v_reuseFailAlloc_3725_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3724_;
            }
            7 => {
                if v_isShared_3730_ == 0 {
                    v___x_3732_ = v___x_3729_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
                    v___x_3732_ = v_reuseFailAlloc_3733_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3732_;
            }
            9 => {
                if v_isShared_3738_ == 0 {
                    v___x_3740_ = v___x_3737_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
                    v___x_3740_ = v_reuseFailAlloc_3741_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed(
    mut v_mvarId_3743_: *mut leanh::LeanObject,
    mut v_type_3744_: *mut leanh::LeanObject,
    mut v_fvars_3745_: *mut leanh::LeanObject,
    mut v_isZero_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
    mut v___y_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isZero_boxed_3752_: u8 = 0;
    let mut v_res_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_3752_ = (leanh::lean_unbox(v_isZero_3746_) as u8);
    v_res_3753_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_3743_, v_type_3744_, v_fvars_3745_, v_isZero_boxed_3752_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
    leanh::lean_dec(v___y_3750_);
    leanh::lean_dec_ref(v___y_3749_);
    leanh::lean_dec(v___y_3748_);
    leanh::lean_dec_ref(v___y_3747_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(
    mut v_lctx_3754_: *mut leanh::LeanObject,
    mut v_x_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyedConfig_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_3762_: u8 = 0;
    let mut v_zetaDeltaSet_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3768_: u8 = 0;
    let mut v_inTypeClassResolution_3769_: u8 = 0;
    let mut v_cacheInferType_3770_: u8 = 0;
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_3761_ = leanh::lean_ctor_get(v___y_3756_, 0);
    v_trackZetaDelta_3762_ = leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_3763_ = leanh::lean_ctor_get(v___y_3756_, 1);
    v_localInstances_3764_ = leanh::lean_ctor_get(v___y_3756_, 3);
    v_defEqCtx_x3f_3765_ = leanh::lean_ctor_get(v___y_3756_, 4);
    v_synthPendingDepth_3766_ = leanh::lean_ctor_get(v___y_3756_, 5);
    v_canUnfold_x3f_3767_ = leanh::lean_ctor_get(v___y_3756_, 6);
    v_univApprox_3768_ = leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_3769_ = leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_3770_ = leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
    );
    leanh::lean_inc(v_canUnfold_x3f_3767_);
    leanh::lean_inc(v_synthPendingDepth_3766_);
    leanh::lean_inc(v_defEqCtx_x3f_3765_);
    leanh::lean_inc_ref(v_localInstances_3764_);
    leanh::lean_inc(v_zetaDeltaSet_3763_);
    leanh::lean_inc_ref(v_keyedConfig_3761_);
    v___x_3771_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_3771_, 0, v_keyedConfig_3761_);
    leanh::lean_ctor_set(v___x_3771_, 1, v_zetaDeltaSet_3763_);
    leanh::lean_ctor_set(v___x_3771_, 2, v_lctx_3754_);
    leanh::lean_ctor_set(v___x_3771_, 3, v_localInstances_3764_);
    leanh::lean_ctor_set(v___x_3771_, 4, v_defEqCtx_x3f_3765_);
    leanh::lean_ctor_set(v___x_3771_, 5, v_synthPendingDepth_3766_);
    leanh::lean_ctor_set(v___x_3771_, 6, v_canUnfold_x3f_3767_);
    leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_3762_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_3768_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_3769_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_3770_,
    );
    leanh::lean_inc(v___y_3759_);
    leanh::lean_inc_ref(v___y_3758_);
    leanh::lean_inc(v___y_3757_);
    v___x_3772_ = leanh::lean_apply_5(
        v_x_3755_,
        v___x_3771_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
        leanh::lean_box(0),
    );
    return v___x_3772_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(
    mut v_lctx_3773_: *mut leanh::LeanObject,
    mut v_x_3774_: *mut leanh::LeanObject,
    mut v___y_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_3773_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
    leanh::lean_dec(v___y_3778_);
    leanh::lean_dec_ref(v___y_3777_);
    leanh::lean_dec(v___y_3776_);
    leanh::lean_dec_ref(v___y_3775_);
    return v_res_3780_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(
    mut v_type_3781_: *mut leanh::LeanObject,
    mut v_mvarId_3782_: *mut leanh::LeanObject,
    mut v_n_3783_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_3784_: *mut leanh::LeanObject,
    mut v___x_3785_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3786_: *mut leanh::LeanObject,
    mut v_lctx_3787_: *mut leanh::LeanObject,
    mut v_fvars_3788_: *mut leanh::LeanObject,
    mut v___x_3789_: *mut leanh::LeanObject,
    mut v_s_3790_: *mut leanh::LeanObject,
    mut v___y_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
    mut v___y_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3796_: u8 = 0;
    let mut v___x_4273__boxed_3797_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3798_: u8 = 0;
    let mut v_res_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3796_ =
        (leanh::lean_unbox(v_preserveBinderNames_3784_) as u8);
    v___x_4273__boxed_3797_ = (leanh::lean_unbox(v___x_3785_) as u8);
    v_useNamesForExplicitOnly_boxed_3798_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_3786_) as u8);
    v_res_3799_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_3781_, v_mvarId_3782_, v_n_3783_, v_preserveBinderNames_boxed_3796_, v___x_4273__boxed_3797_, v_useNamesForExplicitOnly_boxed_3798_, v_lctx_3787_, v_fvars_3788_, v___x_3789_, v_s_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
    leanh::lean_dec(v_n_3783_);
    return v_res_3799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(
    mut v_preserveBinderNames_3800_: u8,
    mut v___x_3801_: u8,
    mut v_useNamesForExplicitOnly_3802_: u8,
    mut v_mvarId_3803_: *mut leanh::LeanObject,
    mut v_i_3804_: *mut leanh::LeanObject,
    mut v_lctx_3805_: *mut leanh::LeanObject,
    mut v_fvars_3806_: *mut leanh::LeanObject,
    mut v_j_3807_: *mut leanh::LeanObject,
    mut v_s_3808_: *mut leanh::LeanObject,
    mut v_type_3809_: *mut leanh::LeanObject,
    mut v_a_3810_: *mut leanh::LeanObject,
    mut v_a_3811_: *mut leanh::LeanObject,
    mut v_a_3812_: *mut leanh::LeanObject,
    mut v_a_3813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3816_: u8 = 0;
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u8 = 0;
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: u8 = 0;
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_a_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3856_: u8 = 0;
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3860_: u8 = 0;
    let mut v_binderName_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3864_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_a_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3815_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3816_ = lean_nat_dec_eq(v_i_3804_, v_zero_3815_);
                if v_isZero_3816_ == 1 {
                    leanh::lean_dec(v_s_3808_);
                    leanh::lean_dec(v_i_3804_);
                    v___x_3817_ = lean_array_get_size(v_fvars_3806_);
                    v_type_3818_ = lean_expr_instantiate_rev_range(
                        v_type_3809_,
                        v_j_3807_,
                        v___x_3817_,
                        v_fvars_3806_,
                    );
                    leanh::lean_dec_ref(v_type_3809_);
                    v___x_3819_ = leanh::lean_box((v_isZero_3816_) as usize);
                    leanh::lean_inc_ref(v_fvars_3806_);
                    v___f_3820_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed as *mut core::ffi::c_void, 9, 4);
                    leanh::lean_closure_set(v___f_3820_, 0, v_mvarId_3803_);
                    leanh::lean_closure_set(v___f_3820_, 1, v_type_3818_);
                    leanh::lean_closure_set(v___f_3820_, 2, v_fvars_3806_);
                    leanh::lean_closure_set(v___f_3820_, 3, v___x_3819_);
                    v___x_3821_ = leanh::lean_alloc_closure(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed as *mut core::ffi::c_void, 9, 4);
                    leanh::lean_closure_set(v___x_3821_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_3821_, 1, v_fvars_3806_);
                    leanh::lean_closure_set(v___x_3821_, 2, v_j_3807_);
                    leanh::lean_closure_set(v___x_3821_, 3, v___f_3820_);
                    v___x_3822_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_3805_, v___x_3821_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                    return v___x_3822_;
                } else {
                    v_one_3823_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3824_ = lean_nat_sub(v_i_3804_, v_one_3823_);
                    leanh::lean_dec(v_i_3804_);
                    match leanh::lean_obj_tag(v_type_3809_) {
                        8 => {
                            v_declName_3825_ = leanh::lean_ctor_get(v_type_3809_, 0);
                            leanh::lean_inc(v_declName_3825_);
                            v_type_3826_ = leanh::lean_ctor_get(v_type_3809_, 1);
                            leanh::lean_inc_ref(v_type_3826_);
                            v_value_3827_ = leanh::lean_ctor_get(v_type_3809_, 2);
                            leanh::lean_inc_ref(v_value_3827_);
                            v_body_3828_ = leanh::lean_ctor_get(v_type_3809_, 3);
                            leanh::lean_inc_ref(v_body_3828_);
                            leanh::lean_dec_ref_known(v_type_3809_, 4);
                            v___x_3829_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                            if leanh::lean_obj_tag(v___x_3829_) == 0 {
                                v_a_3830_ = leanh::lean_ctor_get(v___x_3829_, 0);
                                leanh::lean_inc(v_a_3830_);
                                leanh::lean_dec_ref_known(v___x_3829_, 1);
                                v___x_3831_ = 1;
                                v___x_3832_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_3800_, v___x_3801_, v_useNamesForExplicitOnly_3802_, v_lctx_3805_, v_declName_3825_, v___x_3831_, v_s_3808_, v_a_3812_, v_a_3813_);
                                if leanh::lean_obj_tag(v___x_3832_) == 0 {
                                    v_a_3833_ = leanh::lean_ctor_get(v___x_3832_, 0);
                                    leanh::lean_inc(v_a_3833_);
                                    leanh::lean_dec_ref_known(v___x_3832_, 1);
                                    v_fst_3834_ = leanh::lean_ctor_get(v_a_3833_, 0);
                                    leanh::lean_inc(v_fst_3834_);
                                    v_snd_3835_ = leanh::lean_ctor_get(v_a_3833_, 1);
                                    leanh::lean_inc(v_snd_3835_);
                                    leanh::lean_dec(v_a_3833_);
                                    v___x_3836_ = lean_array_get_size(v_fvars_3806_);
                                    v_type_3837_ = lean_expr_instantiate_rev_range(
                                        v_type_3826_,
                                        v_j_3807_,
                                        v___x_3836_,
                                        v_fvars_3806_,
                                    );
                                    leanh::lean_dec_ref(v_type_3826_);
                                    v_type_3838_ = l_Lean_Expr_headBeta(v_type_3837_);
                                    v_val_3839_ = lean_expr_instantiate_rev_range(
                                        v_value_3827_,
                                        v_j_3807_,
                                        v___x_3836_,
                                        v_fvars_3806_,
                                    );
                                    leanh::lean_dec_ref(v_value_3827_);
                                    v___x_3840_ = 0;
                                    leanh::lean_inc(v_a_3830_);
                                    v___x_3841_ = l_Lean_LocalContext_mkLetDecl(
                                        v_lctx_3805_,
                                        v_a_3830_,
                                        v_fst_3834_,
                                        v_type_3838_,
                                        v_val_3839_,
                                        v_isZero_3816_,
                                        v___x_3840_,
                                    );
                                    v___x_3842_ = l_Lean_mkFVar(v_a_3830_);
                                    v___x_3843_ = lean_array_push(v_fvars_3806_, v___x_3842_);
                                    v_i_3804_ = v_n_3824_;
                                    v_lctx_3805_ = v___x_3841_;
                                    v_fvars_3806_ = v___x_3843_;
                                    v_s_3808_ = v_snd_3835_;
                                    v_type_3809_ = v_body_3828_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3830_);
                                    leanh::lean_dec_ref(v_body_3828_);
                                    leanh::lean_dec_ref(v_value_3827_);
                                    leanh::lean_dec_ref(v_type_3826_);
                                    leanh::lean_dec(v_n_3824_);
                                    leanh::lean_dec(v_j_3807_);
                                    leanh::lean_dec_ref(v_fvars_3806_);
                                    leanh::lean_dec_ref(v_lctx_3805_);
                                    leanh::lean_dec(v_mvarId_3803_);
                                    v_a_3845_ = leanh::lean_ctor_get(v___x_3832_, 0);
                                    v_isSharedCheck_3852_ =
                                        (!leanh::lean_is_exclusive(v___x_3832_)) as u8;
                                    if v_isSharedCheck_3852_ == 0 {
                                        v___x_3847_ = v___x_3832_;
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3845_);
                                        leanh::lean_dec(v___x_3832_);
                                        v___x_3847_ = leanh::lean_box(0);
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_3828_);
                                leanh::lean_dec_ref(v_value_3827_);
                                leanh::lean_dec_ref(v_type_3826_);
                                leanh::lean_dec(v_declName_3825_);
                                leanh::lean_dec(v_n_3824_);
                                leanh::lean_dec(v_s_3808_);
                                leanh::lean_dec(v_j_3807_);
                                leanh::lean_dec_ref(v_fvars_3806_);
                                leanh::lean_dec_ref(v_lctx_3805_);
                                leanh::lean_dec(v_mvarId_3803_);
                                v_a_3853_ = leanh::lean_ctor_get(v___x_3829_, 0);
                                v_isSharedCheck_3860_ =
                                    (!leanh::lean_is_exclusive(v___x_3829_)) as u8;
                                if v_isSharedCheck_3860_ == 0 {
                                    v___x_3855_ = v___x_3829_;
                                    v_isShared_3856_ = v_isSharedCheck_3860_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3853_);
                                    leanh::lean_dec(v___x_3829_);
                                    v___x_3855_ = leanh::lean_box(0);
                                    v_isShared_3856_ = v_isSharedCheck_3860_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        7 => {
                            v_binderName_3861_ = leanh::lean_ctor_get(v_type_3809_, 0);
                            leanh::lean_inc(v_binderName_3861_);
                            v_binderType_3862_ = leanh::lean_ctor_get(v_type_3809_, 1);
                            leanh::lean_inc_ref(v_binderType_3862_);
                            v_body_3863_ = leanh::lean_ctor_get(v_type_3809_, 2);
                            leanh::lean_inc_ref(v_body_3863_);
                            v_binderInfo_3864_ = leanh::lean_ctor_get_uint8(
                                v_type_3809_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            leanh::lean_dec_ref_known(v_type_3809_, 3);
                            v___x_3865_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                            if leanh::lean_obj_tag(v___x_3865_) == 0 {
                                v_a_3866_ = leanh::lean_ctor_get(v___x_3865_, 0);
                                leanh::lean_inc(v_a_3866_);
                                leanh::lean_dec_ref_known(v___x_3865_, 1);
                                v___x_3867_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_3864_);
                                v___x_3868_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_3800_, v___x_3801_, v_useNamesForExplicitOnly_3802_, v_lctx_3805_, v_binderName_3861_, v___x_3867_, v_s_3808_, v_a_3812_, v_a_3813_);
                                if leanh::lean_obj_tag(v___x_3868_) == 0 {
                                    v_a_3869_ = leanh::lean_ctor_get(v___x_3868_, 0);
                                    leanh::lean_inc(v_a_3869_);
                                    leanh::lean_dec_ref_known(v___x_3868_, 1);
                                    v_fst_3870_ = leanh::lean_ctor_get(v_a_3869_, 0);
                                    leanh::lean_inc(v_fst_3870_);
                                    v_snd_3871_ = leanh::lean_ctor_get(v_a_3869_, 1);
                                    leanh::lean_inc(v_snd_3871_);
                                    leanh::lean_dec(v_a_3869_);
                                    v___x_3872_ = lean_array_get_size(v_fvars_3806_);
                                    v_type_3873_ = lean_expr_instantiate_rev_range(
                                        v_binderType_3862_,
                                        v_j_3807_,
                                        v___x_3872_,
                                        v_fvars_3806_,
                                    );
                                    leanh::lean_dec_ref(v_binderType_3862_);
                                    v_type_3874_ = l_Lean_Expr_headBeta(v_type_3873_);
                                    v___x_3875_ = 0;
                                    leanh::lean_inc(v_a_3866_);
                                    v___x_3876_ = l_Lean_LocalContext_mkLocalDecl(
                                        v_lctx_3805_,
                                        v_a_3866_,
                                        v_fst_3870_,
                                        v_type_3874_,
                                        v_binderInfo_3864_,
                                        v___x_3875_,
                                    );
                                    v___x_3877_ = l_Lean_mkFVar(v_a_3866_);
                                    v___x_3878_ = lean_array_push(v_fvars_3806_, v___x_3877_);
                                    v_i_3804_ = v_n_3824_;
                                    v_lctx_3805_ = v___x_3876_;
                                    v_fvars_3806_ = v___x_3878_;
                                    v_s_3808_ = v_snd_3871_;
                                    v_type_3809_ = v_body_3863_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3866_);
                                    leanh::lean_dec_ref(v_body_3863_);
                                    leanh::lean_dec_ref(v_binderType_3862_);
                                    leanh::lean_dec(v_n_3824_);
                                    leanh::lean_dec(v_j_3807_);
                                    leanh::lean_dec_ref(v_fvars_3806_);
                                    leanh::lean_dec_ref(v_lctx_3805_);
                                    leanh::lean_dec(v_mvarId_3803_);
                                    v_a_3880_ = leanh::lean_ctor_get(v___x_3868_, 0);
                                    v_isSharedCheck_3887_ =
                                        (!leanh::lean_is_exclusive(v___x_3868_)) as u8;
                                    if v_isSharedCheck_3887_ == 0 {
                                        v___x_3882_ = v___x_3868_;
                                        v_isShared_3883_ = v_isSharedCheck_3887_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3880_);
                                        leanh::lean_dec(v___x_3868_);
                                        v___x_3882_ = leanh::lean_box(0);
                                        v_isShared_3883_ = v_isSharedCheck_3887_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_3863_);
                                leanh::lean_dec_ref(v_binderType_3862_);
                                leanh::lean_dec(v_binderName_3861_);
                                leanh::lean_dec(v_n_3824_);
                                leanh::lean_dec(v_s_3808_);
                                leanh::lean_dec(v_j_3807_);
                                leanh::lean_dec_ref(v_fvars_3806_);
                                leanh::lean_dec_ref(v_lctx_3805_);
                                leanh::lean_dec(v_mvarId_3803_);
                                v_a_3888_ = leanh::lean_ctor_get(v___x_3865_, 0);
                                v_isSharedCheck_3895_ =
                                    (!leanh::lean_is_exclusive(v___x_3865_)) as u8;
                                if v_isSharedCheck_3895_ == 0 {
                                    v___x_3890_ = v___x_3865_;
                                    v_isShared_3891_ = v_isSharedCheck_3895_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3888_);
                                    leanh::lean_dec(v___x_3865_);
                                    v___x_3890_ = leanh::lean_box(0);
                                    v_isShared_3891_ = v_isSharedCheck_3895_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v___x_3896_ = lean_array_get_size(v_fvars_3806_);
                            v_type_3897_ = lean_expr_instantiate_rev_range(
                                v_type_3809_,
                                v_j_3807_,
                                v___x_3896_,
                                v_fvars_3806_,
                            );
                            leanh::lean_dec_ref(v_type_3809_);
                            v___x_3898_ =
                                leanh::lean_box((v_preserveBinderNames_3800_) as usize);
                            v___x_3899_ = leanh::lean_box((v___x_3801_) as usize);
                            v___x_3900_ =
                                leanh::lean_box((v_useNamesForExplicitOnly_3802_) as usize);
                            leanh::lean_inc_ref(v_fvars_3806_);
                            leanh::lean_inc_ref(v_lctx_3805_);
                            v___f_3901_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed as *mut core::ffi::c_void, 15, 10);
                            leanh::lean_closure_set(v___f_3901_, 0, v_type_3897_);
                            leanh::lean_closure_set(v___f_3901_, 1, v_mvarId_3803_);
                            leanh::lean_closure_set(v___f_3901_, 2, v_n_3824_);
                            leanh::lean_closure_set(v___f_3901_, 3, v___x_3898_);
                            leanh::lean_closure_set(v___f_3901_, 4, v___x_3899_);
                            leanh::lean_closure_set(v___f_3901_, 5, v___x_3900_);
                            leanh::lean_closure_set(v___f_3901_, 6, v_lctx_3805_);
                            leanh::lean_closure_set(v___f_3901_, 7, v_fvars_3806_);
                            leanh::lean_closure_set(v___f_3901_, 8, v___x_3896_);
                            leanh::lean_closure_set(v___f_3901_, 9, v_s_3808_);
                            v___x_3902_ = leanh::lean_alloc_closure(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed as *mut core::ffi::c_void, 9, 4);
                            leanh::lean_closure_set(
                                v___x_3902_,
                                0,
                                leanh::lean_box(0),
                            );
                            leanh::lean_closure_set(v___x_3902_, 1, v_fvars_3806_);
                            leanh::lean_closure_set(v___x_3902_, 2, v_j_3807_);
                            leanh::lean_closure_set(v___x_3902_, 3, v___f_3901_);
                            v___x_3903_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_3805_, v___x_3902_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                            return v___x_3903_;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3848_ == 0 {
                    v___x_3850_ = v___x_3847_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3850_;
            }
            3 => {
                if v_isShared_3856_ == 0 {
                    v___x_3858_ = v___x_3855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
                    v___x_3858_ = v_reuseFailAlloc_3859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3858_;
            }
            5 => {
                if v_isShared_3883_ == 0 {
                    v___x_3885_ = v___x_3882_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
                    v___x_3885_ = v_reuseFailAlloc_3886_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3885_;
            }
            7 => {
                if v_isShared_3891_ == 0 {
                    v___x_3893_ = v___x_3890_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(
    mut v_type_3904_: *mut leanh::LeanObject,
    mut v_mvarId_3905_: *mut leanh::LeanObject,
    mut v_n_3906_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_3907_: u8,
    mut v___x_3908_: u8,
    mut v_useNamesForExplicitOnly_3909_: u8,
    mut v_lctx_3910_: *mut leanh::LeanObject,
    mut v_fvars_3911_: *mut leanh::LeanObject,
    mut v___x_3912_: *mut leanh::LeanObject,
    mut v_s_3913_: *mut leanh::LeanObject,
    mut v___y_3914_: *mut leanh::LeanObject,
    mut v___y_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: u8 = 0;
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3936_: u8 = 0;
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u8 = 0;
    let mut v___x_3945_: u8 = 0;
    let mut v_a_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3949_: u8 = 0;
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3919_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_3904_, v___y_3915_);
                if leanh::lean_obj_tag(v___x_3919_) == 0 {
                    v_a_3920_ = leanh::lean_ctor_get(v___x_3919_, 0);
                    leanh::lean_inc(v_a_3920_);
                    leanh::lean_dec_ref_known(v___x_3919_, 1);
                    v___x_3921_ = l_Lean_Expr_cleanupAnnotations(v_a_3920_);
                    v___x_3944_ = l_Lean_Expr_isForall(v___x_3921_);
                    if v___x_3944_ == 0 {
                        v___x_3945_ = l_Lean_Expr_isLet(v___x_3921_);
                        v___y_3923_ = v___x_3945_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3923_ = v___x_3944_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_3917_);
                    leanh::lean_dec_ref(v___y_3916_);
                    leanh::lean_dec(v___y_3915_);
                    leanh::lean_dec_ref(v___y_3914_);
                    leanh::lean_dec(v_s_3913_);
                    leanh::lean_dec(v___x_3912_);
                    leanh::lean_dec_ref(v_fvars_3911_);
                    leanh::lean_dec_ref(v_lctx_3910_);
                    leanh::lean_dec(v_mvarId_3905_);
                    v_a_3946_ = leanh::lean_ctor_get(v___x_3919_, 0);
                    v_isSharedCheck_3953_ = (!leanh::lean_is_exclusive(v___x_3919_)) as u8;
                    if v_isSharedCheck_3953_ == 0 {
                        v___x_3948_ = v___x_3919_;
                        v_isShared_3949_ = v_isSharedCheck_3953_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3946_);
                        leanh::lean_dec(v___x_3919_);
                        v___x_3948_ = leanh::lean_box(0);
                        v_isShared_3949_ = v_isSharedCheck_3953_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3923_ == 0 {
                    leanh::lean_inc(v___y_3917_);
                    leanh::lean_inc_ref(v___y_3916_);
                    leanh::lean_inc(v___y_3915_);
                    leanh::lean_inc_ref(v___y_3914_);
                    v___x_3924_ = lean_whnf(
                        v___x_3921_,
                        v___y_3914_,
                        v___y_3915_,
                        v___y_3916_,
                        v___y_3917_,
                    );
                    if leanh::lean_obj_tag(v___x_3924_) == 0 {
                        v_a_3925_ = leanh::lean_ctor_get(v___x_3924_, 0);
                        leanh::lean_inc(v_a_3925_);
                        leanh::lean_dec_ref_known(v___x_3924_, 1);
                        v___x_3926_ = l_Lean_Expr_isForall(v_a_3925_);
                        if v___x_3926_ == 0 {
                            leanh::lean_dec(v_a_3925_);
                            leanh::lean_dec(v_s_3913_);
                            leanh::lean_dec(v___x_3912_);
                            leanh::lean_dec_ref(v_fvars_3911_);
                            leanh::lean_dec_ref(v_lctx_3910_);
                            v___x_3927_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                            v___x_3928_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
                            v___x_3929_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_3927_,
                                v_mvarId_3905_,
                                v___x_3928_,
                                v___y_3914_,
                                v___y_3915_,
                                v___y_3916_,
                                v___y_3917_,
                            );
                            leanh::lean_dec(v___y_3917_);
                            leanh::lean_dec_ref(v___y_3916_);
                            leanh::lean_dec(v___y_3915_);
                            leanh::lean_dec_ref(v___y_3914_);
                            return v___x_3929_;
                        } else {
                            v___x_3930_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3931_ = lean_nat_add(v_n_3906_, v___x_3930_);
                            v___x_3932_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_3907_, v___x_3908_, v_useNamesForExplicitOnly_3909_, v_mvarId_3905_, v___x_3931_, v_lctx_3910_, v_fvars_3911_, v___x_3912_, v_s_3913_, v_a_3925_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                            leanh::lean_dec(v___y_3917_);
                            leanh::lean_dec_ref(v___y_3916_);
                            leanh::lean_dec(v___y_3915_);
                            leanh::lean_dec_ref(v___y_3914_);
                            return v___x_3932_;
                        }
                    } else {
                        leanh::lean_dec(v___y_3917_);
                        leanh::lean_dec_ref(v___y_3916_);
                        leanh::lean_dec(v___y_3915_);
                        leanh::lean_dec_ref(v___y_3914_);
                        leanh::lean_dec(v_s_3913_);
                        leanh::lean_dec(v___x_3912_);
                        leanh::lean_dec_ref(v_fvars_3911_);
                        leanh::lean_dec_ref(v_lctx_3910_);
                        leanh::lean_dec(v_mvarId_3905_);
                        v_a_3933_ = leanh::lean_ctor_get(v___x_3924_, 0);
                        v_isSharedCheck_3940_ =
                            (!leanh::lean_is_exclusive(v___x_3924_)) as u8;
                        if v_isSharedCheck_3940_ == 0 {
                            v___x_3935_ = v___x_3924_;
                            v_isShared_3936_ = v_isSharedCheck_3940_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3933_);
                            leanh::lean_dec(v___x_3924_);
                            v___x_3935_ = leanh::lean_box(0);
                            v_isShared_3936_ = v_isSharedCheck_3940_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3941_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3942_ = lean_nat_add(v_n_3906_, v___x_3941_);
                    v___x_3943_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_3907_, v___x_3908_, v_useNamesForExplicitOnly_3909_, v_mvarId_3905_, v___x_3942_, v_lctx_3910_, v_fvars_3911_, v___x_3912_, v_s_3913_, v___x_3921_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                    leanh::lean_dec(v___y_3917_);
                    leanh::lean_dec_ref(v___y_3916_);
                    leanh::lean_dec(v___y_3915_);
                    leanh::lean_dec_ref(v___y_3914_);
                    return v___x_3943_;
                }
            }
            2 => {
                if v_isShared_3936_ == 0 {
                    v___x_3938_ = v___x_3935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3939_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
                    v___x_3938_ = v_reuseFailAlloc_3939_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3938_;
            }
            4 => {
                if v_isShared_3949_ == 0 {
                    v___x_3951_ = v___x_3948_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3952_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
                    v___x_3951_ = v_reuseFailAlloc_3952_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___boxed(
    mut v_preserveBinderNames_3954_: *mut leanh::LeanObject,
    mut v___x_3955_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3956_: *mut leanh::LeanObject,
    mut v_mvarId_3957_: *mut leanh::LeanObject,
    mut v_i_3958_: *mut leanh::LeanObject,
    mut v_lctx_3959_: *mut leanh::LeanObject,
    mut v_fvars_3960_: *mut leanh::LeanObject,
    mut v_j_3961_: *mut leanh::LeanObject,
    mut v_s_3962_: *mut leanh::LeanObject,
    mut v_type_3963_: *mut leanh::LeanObject,
    mut v_a_3964_: *mut leanh::LeanObject,
    mut v_a_3965_: *mut leanh::LeanObject,
    mut v_a_3966_: *mut leanh::LeanObject,
    mut v_a_3967_: *mut leanh::LeanObject,
    mut v_a_3968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3969_: u8 = 0;
    let mut v___x_4306__boxed_3970_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3971_: u8 = 0;
    let mut v_res_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3969_ =
        (leanh::lean_unbox(v_preserveBinderNames_3954_) as u8);
    v___x_4306__boxed_3970_ = (leanh::lean_unbox(v___x_3955_) as u8);
    v_useNamesForExplicitOnly_boxed_3971_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_3956_) as u8);
    v_res_3972_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_3969_, v___x_4306__boxed_3970_, v_useNamesForExplicitOnly_boxed_3971_, v_mvarId_3957_, v_i_3958_, v_lctx_3959_, v_fvars_3960_, v_j_3961_, v_s_3962_, v_type_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
    leanh::lean_dec(v_a_3967_);
    leanh::lean_dec_ref(v_a_3966_);
    leanh::lean_dec(v_a_3965_);
    leanh::lean_dec_ref(v_a_3964_);
    return v_res_3972_;
}
pub unsafe fn l_Lean_Meta_introNCore___lam__0(
    mut v_mvarId_3973_: *mut leanh::LeanObject,
    mut v___x_3974_: *mut leanh::LeanObject,
    mut v___x_3975_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_3976_: u8,
    mut v___x_3977_: u8,
    mut v_useNamesForExplicitOnly_3978_: u8,
    mut v_n_3979_: *mut leanh::LeanObject,
    mut v_givenNames_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v_fst_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_sz_4001_: usize = 0;
    let mut v___x_4002_: usize = 0;
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4010_: u8 = 0;
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v_a_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_a_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut v_a_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3973_);
                v___x_3986_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3973_,
                    v___x_3974_,
                    v___y_3981_,
                    v___y_3982_,
                    v___y_3983_,
                    v___y_3984_,
                );
                if leanh::lean_obj_tag(v___x_3986_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3986_, 1);
                    leanh::lean_inc(v_mvarId_3973_);
                    v___x_3987_ = l_Lean_MVarId_getType(
                        v_mvarId_3973_,
                        v___y_3981_,
                        v___y_3982_,
                        v___y_3983_,
                        v___y_3984_,
                    );
                    if leanh::lean_obj_tag(v___x_3987_) == 0 {
                        v_a_3988_ = leanh::lean_ctor_get(v___x_3987_, 0);
                        leanh::lean_inc(v_a_3988_);
                        leanh::lean_dec_ref_known(v___x_3987_, 1);
                        v_lctx_3989_ = leanh::lean_ctor_get(v___y_3981_, 2);
                        leanh::lean_inc_ref(v_lctx_3989_);
                        v___x_3990_ = lean_mk_empty_array_with_capacity(v___x_3975_);
                        v___x_3991_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_3976_, v___x_3977_, v_useNamesForExplicitOnly_3978_, v_mvarId_3973_, v_n_3979_, v_lctx_3989_, v___x_3990_, v___x_3975_, v_givenNames_3980_, v_a_3988_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
                        leanh::lean_dec_ref(v___y_3981_);
                        if leanh::lean_obj_tag(v___x_3991_) == 0 {
                            v_a_3992_ = leanh::lean_ctor_get(v___x_3991_, 0);
                            v_isSharedCheck_4011_ =
                                (!leanh::lean_is_exclusive(v___x_3991_)) as u8;
                            if v_isSharedCheck_4011_ == 0 {
                                v___x_3994_ = v___x_3991_;
                                v_isShared_3995_ = v_isSharedCheck_4011_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3992_);
                                leanh::lean_dec(v___x_3991_);
                                v___x_3994_ = leanh::lean_box(0);
                                v_isShared_3995_ = v_isSharedCheck_4011_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4012_ = leanh::lean_ctor_get(v___x_3991_, 0);
                            v_isSharedCheck_4019_ =
                                (!leanh::lean_is_exclusive(v___x_3991_)) as u8;
                            if v_isSharedCheck_4019_ == 0 {
                                v___x_4014_ = v___x_3991_;
                                v_isShared_4015_ = v_isSharedCheck_4019_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4012_);
                                leanh::lean_dec(v___x_3991_);
                                v___x_4014_ = leanh::lean_box(0);
                                v_isShared_4015_ = v_isSharedCheck_4019_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3981_);
                        leanh::lean_dec(v_givenNames_3980_);
                        leanh::lean_dec(v_n_3979_);
                        leanh::lean_dec(v___x_3975_);
                        leanh::lean_dec(v_mvarId_3973_);
                        v_a_4020_ = leanh::lean_ctor_get(v___x_3987_, 0);
                        v_isSharedCheck_4027_ =
                            (!leanh::lean_is_exclusive(v___x_3987_)) as u8;
                        if v_isSharedCheck_4027_ == 0 {
                            v___x_4022_ = v___x_3987_;
                            v_isShared_4023_ = v_isSharedCheck_4027_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4020_);
                            leanh::lean_dec(v___x_3987_);
                            v___x_4022_ = leanh::lean_box(0);
                            v_isShared_4023_ = v_isSharedCheck_4027_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3981_);
                    leanh::lean_dec(v_givenNames_3980_);
                    leanh::lean_dec(v_n_3979_);
                    leanh::lean_dec(v___x_3975_);
                    leanh::lean_dec(v_mvarId_3973_);
                    v_a_4028_ = leanh::lean_ctor_get(v___x_3986_, 0);
                    v_isSharedCheck_4035_ = (!leanh::lean_is_exclusive(v___x_3986_)) as u8;
                    if v_isSharedCheck_4035_ == 0 {
                        v___x_4030_ = v___x_3986_;
                        v_isShared_4031_ = v_isSharedCheck_4035_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4028_);
                        leanh::lean_dec(v___x_3986_);
                        v___x_4030_ = leanh::lean_box(0);
                        v_isShared_4031_ = v_isSharedCheck_4035_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3996_ = leanh::lean_ctor_get(v_a_3992_, 0);
                v_snd_3997_ = leanh::lean_ctor_get(v_a_3992_, 1);
                v_isSharedCheck_4010_ = (!leanh::lean_is_exclusive(v_a_3992_)) as u8;
                if v_isSharedCheck_4010_ == 0 {
                    v___x_3999_ = v_a_3992_;
                    v_isShared_4000_ = v_isSharedCheck_4010_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3997_);
                    leanh::lean_inc(v_fst_3996_);
                    leanh::lean_dec(v_a_3992_);
                    v___x_3999_ = leanh::lean_box(0);
                    v_isShared_4000_ = v_isSharedCheck_4010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_4001_ = lean_array_size(v_fst_3996_);
                v___x_4002_ = 0usize;
                v___x_4003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_4001_, v___x_4002_, v_fst_3996_);
                if v_isShared_4000_ == 0 {
                    leanh::lean_ctor_set(v___x_3999_, 0, v___x_4003_);
                    v___x_4005_ = v___x_3999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4009_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_snd_3997_);
                    v___x_4005_ = v_reuseFailAlloc_4009_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3995_ == 0 {
                    leanh::lean_ctor_set(v___x_3994_, 0, v___x_4005_);
                    v___x_4007_ = v___x_3994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4008_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4008_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4007_;
            }
            5 => {
                if v_isShared_4015_ == 0 {
                    v___x_4017_ = v___x_4014_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
                    v___x_4017_ = v_reuseFailAlloc_4018_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4017_;
            }
            7 => {
                if v_isShared_4023_ == 0 {
                    v___x_4025_ = v___x_4022_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
                    v___x_4025_ = v_reuseFailAlloc_4026_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4025_;
            }
            9 => {
                if v_isShared_4031_ == 0 {
                    v___x_4033_ = v___x_4030_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
                    v___x_4033_ = v_reuseFailAlloc_4034_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_introNCore___lam__0___boxed(
    mut v_mvarId_4036_: *mut leanh::LeanObject,
    mut v___x_4037_: *mut leanh::LeanObject,
    mut v___x_4038_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_4039_: *mut leanh::LeanObject,
    mut v___x_4040_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4041_: *mut leanh::LeanObject,
    mut v_n_4042_: *mut leanh::LeanObject,
    mut v_givenNames_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_4049_: u8 = 0;
    let mut v___x_4536__boxed_4050_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_4051_: u8 = 0;
    let mut v_res_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_4049_ =
        (leanh::lean_unbox(v_preserveBinderNames_4039_) as u8);
    v___x_4536__boxed_4050_ = (leanh::lean_unbox(v___x_4040_) as u8);
    v_useNamesForExplicitOnly_boxed_4051_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_4041_) as u8);
    v_res_4052_ = l_Lean_Meta_introNCore___lam__0(
        v_mvarId_4036_,
        v___x_4037_,
        v___x_4038_,
        v_preserveBinderNames_boxed_4049_,
        v___x_4536__boxed_4050_,
        v_useNamesForExplicitOnly_boxed_4051_,
        v_n_4042_,
        v_givenNames_4043_,
        v___y_4044_,
        v___y_4045_,
        v___y_4046_,
        v___y_4047_,
    );
    leanh::lean_dec(v___y_4047_);
    leanh::lean_dec_ref(v___y_4046_);
    leanh::lean_dec(v___y_4045_);
    return v_res_4052_;
}
pub unsafe fn l_Lean_Meta_introNCore(
    mut v_mvarId_4055_: *mut leanh::LeanObject,
    mut v_n_4056_: *mut leanh::LeanObject,
    mut v_givenNames_4057_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4058_: u8,
    mut v_preserveBinderNames_4059_: u8,
    mut v_a_4060_: *mut leanh::LeanObject,
    mut v_a_4061_: *mut leanh::LeanObject,
    mut v_a_4062_: *mut leanh::LeanObject,
    mut v_a_4063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    v___x_4065_ = leanh::lean_unsigned_to_nat(0);
    v___x_4066_ = lean_nat_dec_eq(v_n_4056_, v___x_4065_);
    if v___x_4066_ == 0 {
        let mut v_options_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: u8 = 0;
        let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_options_4067_ = leanh::lean_ctor_get(v_a_4062_, 2);
        v___x_4068_ = l_Lean_Meta_tactic_hygienic;
        v___x_4069_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
            v_options_4067_,
            v___x_4068_,
        );
        v___x_4070_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
        v___x_4071_ = leanh::lean_box((v_preserveBinderNames_4059_) as usize);
        v___x_4072_ = leanh::lean_box((v___x_4069_) as usize);
        v___x_4073_ = leanh::lean_box((v_useNamesForExplicitOnly_4058_) as usize);
        leanh::lean_inc(v_mvarId_4055_);
        v___f_4074_ = leanh::lean_alloc_closure(
            l_Lean_Meta_introNCore___lam__0___boxed as *mut core::ffi::c_void,
            13,
            8,
        );
        leanh::lean_closure_set(v___f_4074_, 0, v_mvarId_4055_);
        leanh::lean_closure_set(v___f_4074_, 1, v___x_4070_);
        leanh::lean_closure_set(v___f_4074_, 2, v___x_4065_);
        leanh::lean_closure_set(v___f_4074_, 3, v___x_4071_);
        leanh::lean_closure_set(v___f_4074_, 4, v___x_4072_);
        leanh::lean_closure_set(v___f_4074_, 5, v___x_4073_);
        leanh::lean_closure_set(v___f_4074_, 6, v_n_4056_);
        leanh::lean_closure_set(v___f_4074_, 7, v_givenNames_4057_);
        v___x_4075_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
            v_mvarId_4055_,
            v___f_4074_,
            v_a_4060_,
            v_a_4061_,
            v_a_4062_,
            v_a_4063_,
        );
        return v___x_4075_;
    } else {
        let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_givenNames_4057_);
        leanh::lean_dec(v_n_4056_);
        v___x_4076_ = l_Lean_Meta_introNCore___closed__0;
        v___x_4077_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4077_, 0, v___x_4076_);
        leanh::lean_ctor_set(v___x_4077_, 1, v_mvarId_4055_);
        v___x_4078_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4078_, 0, v___x_4077_);
        return v___x_4078_;
    }
}
pub unsafe fn l_Lean_Meta_introNCore___boxed(
    mut v_mvarId_4079_: *mut leanh::LeanObject,
    mut v_n_4080_: *mut leanh::LeanObject,
    mut v_givenNames_4081_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4082_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_4083_: *mut leanh::LeanObject,
    mut v_a_4084_: *mut leanh::LeanObject,
    mut v_a_4085_: *mut leanh::LeanObject,
    mut v_a_4086_: *mut leanh::LeanObject,
    mut v_a_4087_: *mut leanh::LeanObject,
    mut v_a_4088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNamesForExplicitOnly_boxed_4089_: u8 = 0;
    let mut v_preserveBinderNames_boxed_4090_: u8 = 0;
    let mut v_res_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNamesForExplicitOnly_boxed_4089_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_4082_) as u8);
    v_preserveBinderNames_boxed_4090_ =
        (leanh::lean_unbox(v_preserveBinderNames_4083_) as u8);
    v_res_4091_ = l_Lean_Meta_introNCore(
        v_mvarId_4079_,
        v_n_4080_,
        v_givenNames_4081_,
        v_useNamesForExplicitOnly_boxed_4089_,
        v_preserveBinderNames_boxed_4090_,
        v_a_4084_,
        v_a_4085_,
        v_a_4086_,
        v_a_4087_,
    );
    leanh::lean_dec(v_a_4087_);
    leanh::lean_dec_ref(v_a_4086_);
    leanh::lean_dec(v_a_4085_);
    leanh::lean_dec_ref(v_a_4084_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(
    mut v_00_u03b1_4092_: *mut leanh::LeanObject,
    mut v_lctx_4093_: *mut leanh::LeanObject,
    mut v_x_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4100_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_4093_, v_x_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
    return v___x_4100_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(
    mut v_00_u03b1_4101_: *mut leanh::LeanObject,
    mut v_lctx_4102_: *mut leanh::LeanObject,
    mut v_x_4103_: *mut leanh::LeanObject,
    mut v___y_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_4101_, v_lctx_4102_, v_x_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
    leanh::lean_dec(v___y_4107_);
    leanh::lean_dec_ref(v___y_4106_);
    leanh::lean_dec(v___y_4105_);
    leanh::lean_dec_ref(v___y_4104_);
    return v_res_4109_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(
    mut v_e_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4116_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_4110_, v___y_4112_);
    return v___x_4116_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(
    mut v_e_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
    leanh::lean_dec(v___y_4121_);
    leanh::lean_dec_ref(v___y_4120_);
    leanh::lean_dec(v___y_4119_);
    leanh::lean_dec_ref(v___y_4118_);
    return v_res_4123_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(
    mut v_mvarId_4124_: *mut leanh::LeanObject,
    mut v_val_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_4124_, v_val_4125_, v___y_4127_);
    return v___x_4131_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(
    mut v_mvarId_4132_: *mut leanh::LeanObject,
    mut v_val_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4139_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_4132_, v_val_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
    leanh::lean_dec(v___y_4137_);
    leanh::lean_dec_ref(v___y_4136_);
    leanh::lean_dec(v___y_4135_);
    leanh::lean_dec_ref(v___y_4134_);
    return v_res_4139_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4140_: *mut leanh::LeanObject,
    mut v_fvars_4141_: *mut leanh::LeanObject,
    mut v_j_4142_: *mut leanh::LeanObject,
    mut v_x_4143_: *mut leanh::LeanObject,
    mut v___y_4144_: *mut leanh::LeanObject,
    mut v___y_4145_: *mut leanh::LeanObject,
    mut v___y_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_4141_, v_j_4142_, v_x_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
    return v___x_4149_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_4150_: *mut leanh::LeanObject,
    mut v_fvars_4151_: *mut leanh::LeanObject,
    mut v_j_4152_: *mut leanh::LeanObject,
    mut v_x_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_4150_, v_fvars_4151_, v_j_4152_, v_x_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
    leanh::lean_dec(v___y_4157_);
    leanh::lean_dec_ref(v___y_4156_);
    leanh::lean_dec(v___y_4155_);
    leanh::lean_dec_ref(v___y_4154_);
    return v_res_4159_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(
    mut v___y_4160_: *mut leanh::LeanObject,
    mut v___y_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
    mut v___y_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_4163_);
    return v___x_4165_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
    leanh::lean_dec(v___y_4169_);
    leanh::lean_dec_ref(v___y_4168_);
    leanh::lean_dec(v___y_4167_);
    leanh::lean_dec_ref(v___y_4166_);
    return v_res_4171_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4172_: *mut leanh::LeanObject,
    mut v_x_4173_: *mut leanh::LeanObject,
    mut v_x_4174_: *mut leanh::LeanObject,
    mut v_x_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_4173_, v_x_4174_, v_x_4175_);
    return v___x_4176_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_4177_: *mut leanh::LeanObject,
    mut v_x_4178_: *mut leanh::LeanObject,
    mut v_x_4179_: usize,
    mut v_x_4180_: usize,
    mut v_x_4181_: *mut leanh::LeanObject,
    mut v_x_4182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_4178_, v_x_4179_, v_x_4180_, v_x_4181_, v_x_4182_);
    return v___x_4183_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_4184_: *mut leanh::LeanObject,
    mut v_x_4185_: *mut leanh::LeanObject,
    mut v_x_4186_: *mut leanh::LeanObject,
    mut v_x_4187_: *mut leanh::LeanObject,
    mut v_x_4188_: *mut leanh::LeanObject,
    mut v_x_4189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4787__boxed_4190_: usize = 0;
    let mut v_x_4788__boxed_4191_: usize = 0;
    let mut v_res_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4787__boxed_4190_ = leanh::lean_unbox_usize(v_x_4186_);
    leanh::lean_dec(v_x_4186_);
    v_x_4788__boxed_4191_ = leanh::lean_unbox_usize(v_x_4187_);
    leanh::lean_dec(v_x_4187_);
    v_res_4192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_4184_, v_x_4185_, v_x_4787__boxed_4190_, v_x_4788__boxed_4191_, v_x_4188_, v_x_4189_);
    return v_res_4192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(
    mut v_00_u03b2_4193_: *mut leanh::LeanObject,
    mut v_n_4194_: *mut leanh::LeanObject,
    mut v_k_4195_: *mut leanh::LeanObject,
    mut v_v_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_4194_, v_k_4195_, v_v_4196_);
    return v___x_4197_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(
    mut v_00_u03b2_4198_: *mut leanh::LeanObject,
    mut v_depth_4199_: usize,
    mut v_keys_4200_: *mut leanh::LeanObject,
    mut v_vals_4201_: *mut leanh::LeanObject,
    mut v_heq_4202_: *mut leanh::LeanObject,
    mut v_i_4203_: *mut leanh::LeanObject,
    mut v_entries_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_4199_, v_keys_4200_, v_vals_4201_, v_i_4203_, v_entries_4204_);
    return v___x_4205_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_00_u03b2_4206_: *mut leanh::LeanObject,
    mut v_depth_4207_: *mut leanh::LeanObject,
    mut v_keys_4208_: *mut leanh::LeanObject,
    mut v_vals_4209_: *mut leanh::LeanObject,
    mut v_heq_4210_: *mut leanh::LeanObject,
    mut v_i_4211_: *mut leanh::LeanObject,
    mut v_entries_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4213_: usize = 0;
    let mut v_res_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4213_ = leanh::lean_unbox_usize(v_depth_4207_);
    leanh::lean_dec(v_depth_4207_);
    v_res_4214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_4206_, v_depth_boxed_4213_, v_keys_4208_, v_vals_4209_, v_heq_4210_, v_i_4211_, v_entries_4212_);
    leanh::lean_dec_ref(v_vals_4209_);
    leanh::lean_dec_ref(v_keys_4208_);
    return v_res_4214_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(
    mut v_00_u03b2_4215_: *mut leanh::LeanObject,
    mut v_x_4216_: *mut leanh::LeanObject,
    mut v_x_4217_: *mut leanh::LeanObject,
    mut v_x_4218_: *mut leanh::LeanObject,
    mut v_x_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_4216_, v_x_4217_, v_x_4218_, v_x_4219_);
    return v___x_4220_;
}
pub unsafe fn l_Lean_MVarId_introN(
    mut v_mvarId_4221_: *mut leanh::LeanObject,
    mut v_n_4222_: *mut leanh::LeanObject,
    mut v_givenNames_4223_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4224_: u8,
    mut v_a_4225_: *mut leanh::LeanObject,
    mut v_a_4226_: *mut leanh::LeanObject,
    mut v_a_4227_: *mut leanh::LeanObject,
    mut v_a_4228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = 0;
    v___x_4231_ = l_Lean_Meta_introNCore(
        v_mvarId_4221_,
        v_n_4222_,
        v_givenNames_4223_,
        v_useNamesForExplicitOnly_4224_,
        v___x_4230_,
        v_a_4225_,
        v_a_4226_,
        v_a_4227_,
        v_a_4228_,
    );
    return v___x_4231_;
}
pub unsafe fn l_Lean_MVarId_introN___boxed(
    mut v_mvarId_4232_: *mut leanh::LeanObject,
    mut v_n_4233_: *mut leanh::LeanObject,
    mut v_givenNames_4234_: *mut leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4235_: *mut leanh::LeanObject,
    mut v_a_4236_: *mut leanh::LeanObject,
    mut v_a_4237_: *mut leanh::LeanObject,
    mut v_a_4238_: *mut leanh::LeanObject,
    mut v_a_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useNamesForExplicitOnly_boxed_4241_: u8 = 0;
    let mut v_res_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useNamesForExplicitOnly_boxed_4241_ =
        (leanh::lean_unbox(v_useNamesForExplicitOnly_4235_) as u8);
    v_res_4242_ = l_Lean_MVarId_introN(
        v_mvarId_4232_,
        v_n_4233_,
        v_givenNames_4234_,
        v_useNamesForExplicitOnly_boxed_4241_,
        v_a_4236_,
        v_a_4237_,
        v_a_4238_,
        v_a_4239_,
    );
    leanh::lean_dec(v_a_4239_);
    leanh::lean_dec_ref(v_a_4238_);
    leanh::lean_dec(v_a_4237_);
    leanh::lean_dec_ref(v_a_4236_);
    return v_res_4242_;
}
pub unsafe fn l_Lean_MVarId_introNP(
    mut v_mvarId_4243_: *mut leanh::LeanObject,
    mut v_n_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
    mut v_a_4246_: *mut leanh::LeanObject,
    mut v_a_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = leanh::lean_box(0);
    v___x_4251_ = 0;
    v___x_4252_ = 1;
    v___x_4253_ = l_Lean_Meta_introNCore(
        v_mvarId_4243_,
        v_n_4244_,
        v___x_4250_,
        v___x_4251_,
        v___x_4252_,
        v_a_4245_,
        v_a_4246_,
        v_a_4247_,
        v_a_4248_,
    );
    return v___x_4253_;
}
pub unsafe fn l_Lean_MVarId_introNP___boxed(
    mut v_mvarId_4254_: *mut leanh::LeanObject,
    mut v_n_4255_: *mut leanh::LeanObject,
    mut v_a_4256_: *mut leanh::LeanObject,
    mut v_a_4257_: *mut leanh::LeanObject,
    mut v_a_4258_: *mut leanh::LeanObject,
    mut v_a_4259_: *mut leanh::LeanObject,
    mut v_a_4260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4261_ = l_Lean_MVarId_introNP(
        v_mvarId_4254_,
        v_n_4255_,
        v_a_4256_,
        v_a_4257_,
        v_a_4258_,
        v_a_4259_,
    );
    leanh::lean_dec(v_a_4259_);
    leanh::lean_dec_ref(v_a_4258_);
    leanh::lean_dec(v_a_4257_);
    leanh::lean_dec_ref(v_a_4256_);
    return v_res_4261_;
}
pub unsafe fn l_Lean_MVarId_intro(
    mut v_mvarId_4262_: *mut leanh::LeanObject,
    mut v_name_4263_: *mut leanh::LeanObject,
    mut v_a_4264_: *mut leanh::LeanObject,
    mut v_a_4265_: *mut leanh::LeanObject,
    mut v_a_4266_: *mut leanh::LeanObject,
    mut v_a_4267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v_fst_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut v_a_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4269_ = leanh::lean_unsigned_to_nat(1);
                v___x_4270_ = leanh::lean_box(0);
                v___x_4271_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4271_, 0, v_name_4263_);
                leanh::lean_ctor_set(v___x_4271_, 1, v___x_4270_);
                v___x_4272_ = 0;
                v___x_4273_ = l_Lean_Meta_introNCore(
                    v_mvarId_4262_,
                    v___x_4269_,
                    v___x_4271_,
                    v___x_4272_,
                    v___x_4272_,
                    v_a_4264_,
                    v_a_4265_,
                    v_a_4266_,
                    v_a_4267_,
                );
                if leanh::lean_obj_tag(v___x_4273_) == 0 {
                    v_a_4274_ = leanh::lean_ctor_get(v___x_4273_, 0);
                    v_isSharedCheck_4293_ = (!leanh::lean_is_exclusive(v___x_4273_)) as u8;
                    if v_isSharedCheck_4293_ == 0 {
                        v___x_4276_ = v___x_4273_;
                        v_isShared_4277_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4274_);
                        leanh::lean_dec(v___x_4273_);
                        v___x_4276_ = leanh::lean_box(0);
                        v_isShared_4277_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4294_ = leanh::lean_ctor_get(v___x_4273_, 0);
                    v_isSharedCheck_4301_ = (!leanh::lean_is_exclusive(v___x_4273_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4296_ = v___x_4273_;
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4294_);
                        leanh::lean_dec(v___x_4273_);
                        v___x_4296_ = leanh::lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4278_ = leanh::lean_ctor_get(v_a_4274_, 0);
                v_snd_4279_ = leanh::lean_ctor_get(v_a_4274_, 1);
                v_isSharedCheck_4292_ = (!leanh::lean_is_exclusive(v_a_4274_)) as u8;
                if v_isSharedCheck_4292_ == 0 {
                    v___x_4281_ = v_a_4274_;
                    v_isShared_4282_ = v_isSharedCheck_4292_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4279_);
                    leanh::lean_inc(v_fst_4278_);
                    leanh::lean_dec(v_a_4274_);
                    v___x_4281_ = leanh::lean_box(0);
                    v_isShared_4282_ = v_isSharedCheck_4292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4283_ = leanh::lean_box(0);
                v___x_4284_ = leanh::lean_unsigned_to_nat(0);
                v___x_4285_ = lean_array_get(v___x_4283_, v_fst_4278_, v___x_4284_);
                leanh::lean_dec(v_fst_4278_);
                if v_isShared_4282_ == 0 {
                    leanh::lean_ctor_set(v___x_4281_, 0, v___x_4285_);
                    v___x_4287_ = v___x_4281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4291_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_snd_4279_);
                    v___x_4287_ = v_reuseFailAlloc_4291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4277_ == 0 {
                    leanh::lean_ctor_set(v___x_4276_, 0, v___x_4287_);
                    v___x_4289_ = v___x_4276_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4289_;
            }
            5 => {
                if v_isShared_4297_ == 0 {
                    v___x_4299_ = v___x_4296_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_intro___boxed(
    mut v_mvarId_4302_: *mut leanh::LeanObject,
    mut v_name_4303_: *mut leanh::LeanObject,
    mut v_a_4304_: *mut leanh::LeanObject,
    mut v_a_4305_: *mut leanh::LeanObject,
    mut v_a_4306_: *mut leanh::LeanObject,
    mut v_a_4307_: *mut leanh::LeanObject,
    mut v_a_4308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4309_ = l_Lean_MVarId_intro(
        v_mvarId_4302_,
        v_name_4303_,
        v_a_4304_,
        v_a_4305_,
        v_a_4306_,
        v_a_4307_,
    );
    leanh::lean_dec(v_a_4307_);
    leanh::lean_dec_ref(v_a_4306_);
    leanh::lean_dec(v_a_4305_);
    leanh::lean_dec_ref(v_a_4304_);
    return v_res_4309_;
}
pub unsafe fn l_Lean_Meta_intro1Core(
    mut v_mvarId_4310_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_4311_: u8,
    mut v_a_4312_: *mut leanh::LeanObject,
    mut v_a_4313_: *mut leanh::LeanObject,
    mut v_a_4314_: *mut leanh::LeanObject,
    mut v_a_4315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v_fst_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4339_: u8 = 0;
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v_a_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4317_ = leanh::lean_unsigned_to_nat(1);
                v___x_4318_ = leanh::lean_box(0);
                v___x_4319_ = 0;
                v___x_4320_ = l_Lean_Meta_introNCore(
                    v_mvarId_4310_,
                    v___x_4317_,
                    v___x_4318_,
                    v___x_4319_,
                    v_preserveBinderNames_4311_,
                    v_a_4312_,
                    v_a_4313_,
                    v_a_4314_,
                    v_a_4315_,
                );
                if leanh::lean_obj_tag(v___x_4320_) == 0 {
                    v_a_4321_ = leanh::lean_ctor_get(v___x_4320_, 0);
                    v_isSharedCheck_4340_ = (!leanh::lean_is_exclusive(v___x_4320_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v___x_4323_ = v___x_4320_;
                        v_isShared_4324_ = v_isSharedCheck_4340_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4321_);
                        leanh::lean_dec(v___x_4320_);
                        v___x_4323_ = leanh::lean_box(0);
                        v_isShared_4324_ = v_isSharedCheck_4340_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4341_ = leanh::lean_ctor_get(v___x_4320_, 0);
                    v_isSharedCheck_4348_ = (!leanh::lean_is_exclusive(v___x_4320_)) as u8;
                    if v_isSharedCheck_4348_ == 0 {
                        v___x_4343_ = v___x_4320_;
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4341_);
                        leanh::lean_dec(v___x_4320_);
                        v___x_4343_ = leanh::lean_box(0);
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4325_ = leanh::lean_ctor_get(v_a_4321_, 0);
                v_snd_4326_ = leanh::lean_ctor_get(v_a_4321_, 1);
                v_isSharedCheck_4339_ = (!leanh::lean_is_exclusive(v_a_4321_)) as u8;
                if v_isSharedCheck_4339_ == 0 {
                    v___x_4328_ = v_a_4321_;
                    v_isShared_4329_ = v_isSharedCheck_4339_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4326_);
                    leanh::lean_inc(v_fst_4325_);
                    leanh::lean_dec(v_a_4321_);
                    v___x_4328_ = leanh::lean_box(0);
                    v_isShared_4329_ = v_isSharedCheck_4339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4330_ = leanh::lean_box(0);
                v___x_4331_ = leanh::lean_unsigned_to_nat(0);
                v___x_4332_ = lean_array_get(v___x_4330_, v_fst_4325_, v___x_4331_);
                leanh::lean_dec(v_fst_4325_);
                if v_isShared_4329_ == 0 {
                    leanh::lean_ctor_set(v___x_4328_, 0, v___x_4332_);
                    v___x_4334_ = v___x_4328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_snd_4326_);
                    v___x_4334_ = v_reuseFailAlloc_4338_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4324_ == 0 {
                    leanh::lean_ctor_set(v___x_4323_, 0, v___x_4334_);
                    v___x_4336_ = v___x_4323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4336_;
            }
            5 => {
                if v_isShared_4344_ == 0 {
                    v___x_4346_ = v___x_4343_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
                    v___x_4346_ = v_reuseFailAlloc_4347_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_intro1Core___boxed(
    mut v_mvarId_4349_: *mut leanh::LeanObject,
    mut v_preserveBinderNames_4350_: *mut leanh::LeanObject,
    mut v_a_4351_: *mut leanh::LeanObject,
    mut v_a_4352_: *mut leanh::LeanObject,
    mut v_a_4353_: *mut leanh::LeanObject,
    mut v_a_4354_: *mut leanh::LeanObject,
    mut v_a_4355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_4356_: u8 = 0;
    let mut v_res_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_4356_ =
        (leanh::lean_unbox(v_preserveBinderNames_4350_) as u8);
    v_res_4357_ = l_Lean_Meta_intro1Core(
        v_mvarId_4349_,
        v_preserveBinderNames_boxed_4356_,
        v_a_4351_,
        v_a_4352_,
        v_a_4353_,
        v_a_4354_,
    );
    leanh::lean_dec(v_a_4354_);
    leanh::lean_dec_ref(v_a_4353_);
    leanh::lean_dec(v_a_4352_);
    leanh::lean_dec_ref(v_a_4351_);
    return v_res_4357_;
}
pub unsafe fn l_Lean_MVarId_intro1(
    mut v_mvarId_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
    mut v_a_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = 0;
    v___x_4365_ = l_Lean_Meta_intro1Core(
        v_mvarId_4358_,
        v___x_4364_,
        v_a_4359_,
        v_a_4360_,
        v_a_4361_,
        v_a_4362_,
    );
    return v___x_4365_;
}
pub unsafe fn l_Lean_MVarId_intro1___boxed(
    mut v_mvarId_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
    mut v_a_4368_: *mut leanh::LeanObject,
    mut v_a_4369_: *mut leanh::LeanObject,
    mut v_a_4370_: *mut leanh::LeanObject,
    mut v_a_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4372_ = l_Lean_MVarId_intro1(v_mvarId_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
    leanh::lean_dec(v_a_4370_);
    leanh::lean_dec_ref(v_a_4369_);
    leanh::lean_dec(v_a_4368_);
    leanh::lean_dec_ref(v_a_4367_);
    return v_res_4372_;
}
pub unsafe fn l_Lean_MVarId_intro1P(
    mut v_mvarId_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
    mut v_a_4377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4379_ = 1;
    v___x_4380_ = l_Lean_Meta_intro1Core(
        v_mvarId_4373_,
        v___x_4379_,
        v_a_4374_,
        v_a_4375_,
        v_a_4376_,
        v_a_4377_,
    );
    return v___x_4380_;
}
pub unsafe fn l_Lean_MVarId_intro1P___boxed(
    mut v_mvarId_4381_: *mut leanh::LeanObject,
    mut v_a_4382_: *mut leanh::LeanObject,
    mut v_a_4383_: *mut leanh::LeanObject,
    mut v_a_4384_: *mut leanh::LeanObject,
    mut v_a_4385_: *mut leanh::LeanObject,
    mut v_a_4386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Lean_MVarId_intro1P(v_mvarId_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
    leanh::lean_dec(v_a_4385_);
    leanh::lean_dec_ref(v_a_4384_);
    leanh::lean_dec(v_a_4383_);
    leanh::lean_dec_ref(v_a_4382_);
    return v_res_4387_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(
    mut v_msgData_4388_: *mut leanh::LeanObject,
    mut v___y_4389_: *mut leanh::LeanObject,
    mut v___y_4390_: *mut leanh::LeanObject,
    mut v___y_4391_: *mut leanh::LeanObject,
    mut v___y_4392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ = lean_st_ref_get(v___y_4392_);
    v_env_4395_ = leanh::lean_ctor_get(v___x_4394_, 0);
    leanh::lean_inc_ref(v_env_4395_);
    leanh::lean_dec(v___x_4394_);
    v___x_4396_ = lean_st_ref_get(v___y_4390_);
    v_mctx_4397_ = leanh::lean_ctor_get(v___x_4396_, 0);
    leanh::lean_inc_ref(v_mctx_4397_);
    leanh::lean_dec(v___x_4396_);
    v_lctx_4398_ = leanh::lean_ctor_get(v___y_4389_, 2);
    v_options_4399_ = leanh::lean_ctor_get(v___y_4391_, 2);
    leanh::lean_inc_ref(v_options_4399_);
    leanh::lean_inc_ref(v_lctx_4398_);
    v___x_4400_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4400_, 0, v_env_4395_);
    leanh::lean_ctor_set(v___x_4400_, 1, v_mctx_4397_);
    leanh::lean_ctor_set(v___x_4400_, 2, v_lctx_4398_);
    leanh::lean_ctor_set(v___x_4400_, 3, v_options_4399_);
    v___x_4401_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4401_, 0, v___x_4400_);
    leanh::lean_ctor_set(v___x_4401_, 1, v_msgData_4388_);
    v___x_4402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4401_);
    return v___x_4402_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(
    mut v_msgData_4403_: *mut leanh::LeanObject,
    mut v___y_4404_: *mut leanh::LeanObject,
    mut v___y_4405_: *mut leanh::LeanObject,
    mut v___y_4406_: *mut leanh::LeanObject,
    mut v___y_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
    leanh::lean_dec(v___y_4407_);
    leanh::lean_dec_ref(v___y_4406_);
    leanh::lean_dec(v___y_4405_);
    leanh::lean_dec_ref(v___y_4404_);
    return v_res_4409_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
    mut v_msg_4410_: *mut leanh::LeanObject,
    mut v___y_4411_: *mut leanh::LeanObject,
    mut v___y_4412_: *mut leanh::LeanObject,
    mut v___y_4413_: *mut leanh::LeanObject,
    mut v___y_4414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4416_ = leanh::lean_ctor_get(v___y_4413_, 5);
                v___x_4417_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
                v_a_4418_ = leanh::lean_ctor_get(v___x_4417_, 0);
                v_isSharedCheck_4426_ = (!leanh::lean_is_exclusive(v___x_4417_)) as u8;
                if v_isSharedCheck_4426_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    v_isShared_4421_ = v_isSharedCheck_4426_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4418_);
                    leanh::lean_dec(v___x_4417_);
                    v___x_4420_ = leanh::lean_box(0);
                    v_isShared_4421_ = v_isSharedCheck_4426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4416_);
                v___x_4422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4422_, 0, v_ref_4416_);
                leanh::lean_ctor_set(v___x_4422_, 1, v_a_4418_);
                if v_isShared_4421_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4420_, 1);
                    leanh::lean_ctor_set(v___x_4420_, 0, v___x_4422_);
                    v___x_4424_ = v___x_4420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4424_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg___boxed(
    mut v_msg_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4433_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
        v_msg_4427_,
        v___y_4428_,
        v___y_4429_,
        v___y_4430_,
        v___y_4431_,
    );
    leanh::lean_dec(v___y_4431_);
    leanh::lean_dec_ref(v___y_4430_);
    leanh::lean_dec(v___y_4429_);
    leanh::lean_dec_ref(v___y_4428_);
    return v_res_4433_;
}
pub unsafe fn _init_l_Lean_MVarId_intro1___00__lam__0___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = l_Lean_MVarId_intro1___00__lam__0___closed__0;
    v___x_4436_ = l_Lean_stringToMessageData(v___x_4435_);
    return v___x_4436_;
}
pub unsafe fn l_Lean_MVarId_intro1___00__lam__0(
    mut v_mvarId_4437_: *mut leanh::LeanObject,
    mut v___y_4438_: *mut leanh::LeanObject,
    mut v___y_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
    mut v___y_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4448_: u8 = 0;
    let mut v___y_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_unused_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_a_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4497_: u8 = 0;
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_4437_);
                v___x_4443_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_4437_,
                    v___y_4438_,
                    v___y_4439_,
                    v___y_4440_,
                    v___y_4441_,
                );
                if leanh::lean_obj_tag(v___x_4443_) == 0 {
                    v_a_4444_ = leanh::lean_ctor_get(v___x_4443_, 0);
                    leanh::lean_inc(v_a_4444_);
                    leanh::lean_dec_ref_known(v___x_4443_, 1);
                    if leanh::lean_obj_tag(v_a_4444_) == 7 {
                        v_binderName_4445_ = leanh::lean_ctor_get(v_a_4444_, 0);
                        leanh::lean_inc(v_binderName_4445_);
                        v_binderType_4446_ = leanh::lean_ctor_get(v_a_4444_, 1);
                        leanh::lean_inc_ref(v_binderType_4446_);
                        v_body_4447_ = leanh::lean_ctor_get(v_a_4444_, 2);
                        leanh::lean_inc_ref(v_body_4447_);
                        v_binderInfo_4448_ = leanh::lean_ctor_get_uint8(
                            v_a_4444_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_4444_, 3);
                        v___x_4485_ = l_Lean_Expr_hasLooseBVars(v_body_4447_);
                        if v___x_4485_ == 0 {
                            v___y_4450_ = v___y_4438_;
                            v___y_4451_ = v___y_4439_;
                            v___y_4452_ = v___y_4440_;
                            v___y_4453_ = v___y_4441_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_body_4447_);
                            leanh::lean_dec_ref(v_binderType_4446_);
                            leanh::lean_dec(v_binderName_4445_);
                            v___x_4486_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_intro1___00__lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_intro1___00__lam__0___closed__1_once
                                ),
                                _init_l_Lean_MVarId_intro1___00__lam__0___closed__1,
                            );
                            v___x_4487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4487_, 0, v_mvarId_4437_);
                            v___x_4488_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4488_, 0, v___x_4486_);
                            leanh::lean_ctor_set(v___x_4488_, 1, v___x_4487_);
                            v___x_4489_ =
                                l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
                                    v___x_4488_,
                                    v___y_4438_,
                                    v___y_4439_,
                                    v___y_4440_,
                                    v___y_4441_,
                                );
                            v_a_4490_ = leanh::lean_ctor_get(v___x_4489_, 0);
                            v_isSharedCheck_4497_ =
                                (!leanh::lean_is_exclusive(v___x_4489_)) as u8;
                            if v_isSharedCheck_4497_ == 0 {
                                v___x_4492_ = v___x_4489_;
                                v_isShared_4493_ = v_isSharedCheck_4497_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4490_);
                                leanh::lean_dec(v___x_4489_);
                                v___x_4492_ = leanh::lean_box(0);
                                v_isShared_4493_ = v_isSharedCheck_4497_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4444_);
                        v___x_4498_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_intro1___00__lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_intro1___00__lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_intro1___00__lam__0___closed__1,
                        );
                        v___x_4499_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4499_, 0, v_mvarId_4437_);
                        v___x_4500_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4500_, 0, v___x_4498_);
                        leanh::lean_ctor_set(v___x_4500_, 1, v___x_4499_);
                        v___x_4501_ =
                            l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
                                v___x_4500_,
                                v___y_4438_,
                                v___y_4439_,
                                v___y_4440_,
                                v___y_4441_,
                            );
                        return v___x_4501_;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_4437_);
                    v_a_4502_ = leanh::lean_ctor_get(v___x_4443_, 0);
                    v_isSharedCheck_4509_ = (!leanh::lean_is_exclusive(v___x_4443_)) as u8;
                    if v_isSharedCheck_4509_ == 0 {
                        v___x_4504_ = v___x_4443_;
                        v_isShared_4505_ = v_isSharedCheck_4509_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4502_);
                        leanh::lean_dec(v___x_4443_);
                        v___x_4504_ = leanh::lean_box(0);
                        v_isShared_4505_ = v_isSharedCheck_4509_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_mvarId_4437_);
                v___x_4454_ = l_Lean_MVarId_getTag(
                    v_mvarId_4437_,
                    v___y_4450_,
                    v___y_4451_,
                    v___y_4452_,
                    v___y_4453_,
                );
                if leanh::lean_obj_tag(v___x_4454_) == 0 {
                    v_a_4455_ = leanh::lean_ctor_get(v___x_4454_, 0);
                    leanh::lean_inc(v_a_4455_);
                    leanh::lean_dec_ref_known(v___x_4454_, 1);
                    v___x_4456_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_body_4447_,
                        v_a_4455_,
                        v___y_4450_,
                        v___y_4451_,
                        v___y_4452_,
                        v___y_4453_,
                    );
                    if leanh::lean_obj_tag(v___x_4456_) == 0 {
                        v_a_4457_ = leanh::lean_ctor_get(v___x_4456_, 0);
                        leanh::lean_inc_n(v_a_4457_, 2);
                        leanh::lean_dec_ref_known(v___x_4456_, 1);
                        v___x_4458_ = l_Lean_Expr_lam___override(
                            v_binderName_4445_,
                            v_binderType_4446_,
                            v_a_4457_,
                            v_binderInfo_4448_,
                        );
                        v___x_4459_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_4437_, v___x_4458_, v___y_4451_);
                        v_isSharedCheck_4467_ =
                            (!leanh::lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4467_ == 0 {
                            v_unused_4468_ = leanh::lean_ctor_get(v___x_4459_, 0);
                            leanh::lean_dec(v_unused_4468_);
                            v___x_4461_ = v___x_4459_;
                            v_isShared_4462_ = v_isSharedCheck_4467_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4459_);
                            v___x_4461_ = leanh::lean_box(0);
                            v_isShared_4462_ = v_isSharedCheck_4467_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_binderType_4446_);
                        leanh::lean_dec(v_binderName_4445_);
                        leanh::lean_dec(v_mvarId_4437_);
                        v_a_4469_ = leanh::lean_ctor_get(v___x_4456_, 0);
                        v_isSharedCheck_4476_ =
                            (!leanh::lean_is_exclusive(v___x_4456_)) as u8;
                        if v_isSharedCheck_4476_ == 0 {
                            v___x_4471_ = v___x_4456_;
                            v_isShared_4472_ = v_isSharedCheck_4476_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4469_);
                            leanh::lean_dec(v___x_4456_);
                            v___x_4471_ = leanh::lean_box(0);
                            v_isShared_4472_ = v_isSharedCheck_4476_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_body_4447_);
                    leanh::lean_dec_ref(v_binderType_4446_);
                    leanh::lean_dec(v_binderName_4445_);
                    leanh::lean_dec(v_mvarId_4437_);
                    v_a_4477_ = leanh::lean_ctor_get(v___x_4454_, 0);
                    v_isSharedCheck_4484_ = (!leanh::lean_is_exclusive(v___x_4454_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4479_ = v___x_4454_;
                        v_isShared_4480_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4477_);
                        leanh::lean_dec(v___x_4454_);
                        v___x_4479_ = leanh::lean_box(0);
                        v_isShared_4480_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4463_ = l_Lean_Expr_mvarId_x21(v_a_4457_);
                leanh::lean_dec(v_a_4457_);
                if v_isShared_4462_ == 0 {
                    leanh::lean_ctor_set(v___x_4461_, 0, v___x_4463_);
                    v___x_4465_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
                    v___x_4465_ = v_reuseFailAlloc_4466_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4465_;
            }
            4 => {
                if v_isShared_4472_ == 0 {
                    v___x_4474_ = v___x_4471_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
                    v___x_4474_ = v_reuseFailAlloc_4475_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4474_;
            }
            6 => {
                if v_isShared_4480_ == 0 {
                    v___x_4482_ = v___x_4479_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
                    v___x_4482_ = v_reuseFailAlloc_4483_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4482_;
            }
            8 => {
                if v_isShared_4493_ == 0 {
                    v___x_4495_ = v___x_4492_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
                    v___x_4495_ = v_reuseFailAlloc_4496_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4495_;
            }
            10 => {
                if v_isShared_4505_ == 0 {
                    v___x_4507_ = v___x_4504_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4508_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_intro1___00__lam__0___boxed(
    mut v_mvarId_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_MVarId_intro1___00__lam__0(
        v_mvarId_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
    );
    leanh::lean_dec(v___y_4514_);
    leanh::lean_dec_ref(v___y_4513_);
    leanh::lean_dec(v___y_4512_);
    leanh::lean_dec_ref(v___y_4511_);
    return v_res_4516_;
}
pub unsafe fn l_Lean_MVarId_intro1__(
    mut v_mvarId_4517_: *mut leanh::LeanObject,
    mut v_a_4518_: *mut leanh::LeanObject,
    mut v_a_4519_: *mut leanh::LeanObject,
    mut v_a_4520_: *mut leanh::LeanObject,
    mut v_a_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_4517_);
    v___f_4523_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_intro1___00__lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_4523_, 0, v_mvarId_4517_);
    v___x_4524_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
        v_mvarId_4517_,
        v___f_4523_,
        v_a_4518_,
        v_a_4519_,
        v_a_4520_,
        v_a_4521_,
    );
    return v___x_4524_;
}
pub unsafe fn l_Lean_MVarId_intro1___00__boxed(
    mut v_mvarId_4525_: *mut leanh::LeanObject,
    mut v_a_4526_: *mut leanh::LeanObject,
    mut v_a_4527_: *mut leanh::LeanObject,
    mut v_a_4528_: *mut leanh::LeanObject,
    mut v_a_4529_: *mut leanh::LeanObject,
    mut v_a_4530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ =
        l_Lean_MVarId_intro1__(v_mvarId_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
    leanh::lean_dec(v_a_4529_);
    leanh::lean_dec_ref(v_a_4528_);
    leanh::lean_dec(v_a_4527_);
    leanh::lean_dec_ref(v_a_4526_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(
    mut v_00_u03b1_4532_: *mut leanh::LeanObject,
    mut v_msg_4533_: *mut leanh::LeanObject,
    mut v___y_4534_: *mut leanh::LeanObject,
    mut v___y_4535_: *mut leanh::LeanObject,
    mut v___y_4536_: *mut leanh::LeanObject,
    mut v___y_4537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4539_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
        v_msg_4533_,
        v___y_4534_,
        v___y_4535_,
        v___y_4536_,
        v___y_4537_,
    );
    return v___x_4539_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___boxed(
    mut v_00_u03b1_4540_: *mut leanh::LeanObject,
    mut v_msg_4541_: *mut leanh::LeanObject,
    mut v___y_4542_: *mut leanh::LeanObject,
    mut v___y_4543_: *mut leanh::LeanObject,
    mut v___y_4544_: *mut leanh::LeanObject,
    mut v___y_4545_: *mut leanh::LeanObject,
    mut v___y_4546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4547_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(
        v_00_u03b1_4540_,
        v_msg_4541_,
        v___y_4542_,
        v___y_4543_,
        v___y_4544_,
        v___y_4545_,
    );
    leanh::lean_dec(v___y_4545_);
    leanh::lean_dec_ref(v___y_4544_);
    leanh::lean_dec(v___y_4543_);
    leanh::lean_dec_ref(v___y_4542_);
    return v_res_4547_;
}
pub unsafe fn l_Lean_Meta_getIntrosSize(
    mut v_x_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_body_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4548_) {
                7 => {
                    v_body_4549_ = leanh::lean_ctor_get(v_x_4548_, 2);
                    v___x_4550_ = l_Lean_Meta_getIntrosSize(v_body_4549_);
                    v___x_4551_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4552_ = lean_nat_add(v___x_4550_, v___x_4551_);
                    leanh::lean_dec(v___x_4550_);
                    return v___x_4552_;
                }
                8 => {
                    v_body_4553_ = leanh::lean_ctor_get(v_x_4548_, 3);
                    v___x_4554_ = l_Lean_Meta_getIntrosSize(v_body_4553_);
                    v___x_4555_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4556_ = lean_nat_add(v___x_4554_, v___x_4555_);
                    leanh::lean_dec(v___x_4554_);
                    return v___x_4556_;
                }
                10 => {
                    v_expr_4557_ = leanh::lean_ctor_get(v_x_4548_, 1);
                    v_x_4548_ = v_expr_4557_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_4559_ = leanh::lean_unsigned_to_nat(0);
                    return v___x_4559_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getIntrosSize___boxed(
    mut v_x_4560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Lean_Meta_getIntrosSize(v_x_4560_);
    leanh::lean_dec_ref(v_x_4560_);
    return v_res_4561_;
}
pub unsafe fn l_Lean_MVarId_intros(
    mut v_mvarId_4562_: *mut leanh::LeanObject,
    mut v_a_4563_: *mut leanh::LeanObject,
    mut v_a_4564_: *mut leanh::LeanObject,
    mut v_a_4565_: *mut leanh::LeanObject,
    mut v_a_4566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_a_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4589_: u8 = 0;
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_4562_);
                v___x_4568_ = l_Lean_MVarId_getType(
                    v_mvarId_4562_,
                    v_a_4563_,
                    v_a_4564_,
                    v_a_4565_,
                    v_a_4566_,
                );
                if leanh::lean_obj_tag(v___x_4568_) == 0 {
                    v_a_4569_ = leanh::lean_ctor_get(v___x_4568_, 0);
                    leanh::lean_inc(v_a_4569_);
                    leanh::lean_dec_ref_known(v___x_4568_, 1);
                    v___x_4570_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_4569_, v_a_4564_);
                    v_a_4571_ = leanh::lean_ctor_get(v___x_4570_, 0);
                    v_isSharedCheck_4585_ = (!leanh::lean_is_exclusive(v___x_4570_)) as u8;
                    if v_isSharedCheck_4585_ == 0 {
                        v___x_4573_ = v___x_4570_;
                        v_isShared_4574_ = v_isSharedCheck_4585_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4571_);
                        leanh::lean_dec(v___x_4570_);
                        v___x_4573_ = leanh::lean_box(0);
                        v_isShared_4574_ = v_isSharedCheck_4585_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_4562_);
                    v_a_4586_ = leanh::lean_ctor_get(v___x_4568_, 0);
                    v_isSharedCheck_4593_ = (!leanh::lean_is_exclusive(v___x_4568_)) as u8;
                    if v_isSharedCheck_4593_ == 0 {
                        v___x_4588_ = v___x_4568_;
                        v_isShared_4589_ = v_isSharedCheck_4593_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4586_);
                        leanh::lean_dec(v___x_4568_);
                        v___x_4588_ = leanh::lean_box(0);
                        v_isShared_4589_ = v_isSharedCheck_4593_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4575_ = l_Lean_Meta_getIntrosSize(v_a_4571_);
                leanh::lean_dec(v_a_4571_);
                v___x_4576_ = leanh::lean_unsigned_to_nat(0);
                v___x_4577_ = lean_nat_dec_eq(v___x_4575_, v___x_4576_);
                if v___x_4577_ == 0 {
                    leanh::lean_del_object(v___x_4573_);
                    v___x_4578_ = leanh::lean_box(0);
                    v___x_4579_ = l_Lean_Meta_introNCore(
                        v_mvarId_4562_,
                        v___x_4575_,
                        v___x_4578_,
                        v___x_4577_,
                        v___x_4577_,
                        v_a_4563_,
                        v_a_4564_,
                        v_a_4565_,
                        v_a_4566_,
                    );
                    return v___x_4579_;
                } else {
                    leanh::lean_dec(v___x_4575_);
                    v___x_4580_ = l_Lean_Meta_introNCore___closed__0;
                    v___x_4581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4581_, 0, v___x_4580_);
                    leanh::lean_ctor_set(v___x_4581_, 1, v_mvarId_4562_);
                    if v_isShared_4574_ == 0 {
                        leanh::lean_ctor_set(v___x_4573_, 0, v___x_4581_);
                        v___x_4583_ = v___x_4573_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4581_);
                        v___x_4583_ = v_reuseFailAlloc_4584_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4583_;
            }
            3 => {
                if v_isShared_4589_ == 0 {
                    v___x_4591_ = v___x_4588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4592_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
                    v___x_4591_ = v_reuseFailAlloc_4592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_intros___boxed(
    mut v_mvarId_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
    mut v_a_4597_: *mut leanh::LeanObject,
    mut v_a_4598_: *mut leanh::LeanObject,
    mut v_a_4599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4600_ = l_Lean_MVarId_intros(v_mvarId_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
    leanh::lean_dec(v_a_4598_);
    leanh::lean_dec_ref(v_a_4597_);
    leanh::lean_dec(v_a_4596_);
    leanh::lean_dec_ref(v_a_4595_);
    return v_res_4600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Intro(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_tactic_hygienic = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_tactic_hygienic);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Intro(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Intro(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Intro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Intro(builtin);
}