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
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 116, 114, 111, 78, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,3126221519840457472 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<75> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [84, 104, 101, 114, 101, 32, 97, 114, 101, 32, 110, 111, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 98, 105, 110, 100, 101, 114, 115, 32, 111, 114, 32, 96, 108, 101, 116, 96, 32, 98, 105, 110, 100, 105, 110, 103, 115, 32, 105, 110, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 116, 111, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7_value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0_value:
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
    m_fun: l_Lean_Expr_fvarId_x21___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16145843736367156323 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10812791644248028522 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [109, 97, 107, 101, 32, 115, 117, 114, 101, 32, 116, 97, 99, 116, 105, 99, 115, 32, 97, 114, 101, 32, 104, 121, 103, 105, 101, 110, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9078769453211668998 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3519807978581637299 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_tactic_hygienic: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13286986945483979944 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_introNCore___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_introNCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_introNCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_intro1___00__lam__0___closed__0_value: crate::leanh::LeanStringObject<30> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_intro1___00__lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_intro1___00__lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_intro1___00__lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_intro1___00__lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0(
    mut v_mvarId_2301_: *mut crate::leanh::LeanObject,
    mut v_type_2302_: *mut crate::leanh::LeanObject,
    mut v_fvars_2303_: *mut crate::leanh::LeanObject,
    mut v_isZero_2304_: u8,
    mut v___x_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533__overap_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_unused_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut v_a_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2347_: u8 = 0;
    let mut v_a_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2351_: u8 = 0;
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut v_a_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2359_: u8 = 0;
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2301_);
                v___x_2311_ = l_Lean_MVarId_getTag(
                    v_mvarId_2301_,
                    v___y_2306_,
                    v___y_2307_,
                    v___y_2308_,
                    v___y_2309_,
                );
                if crate::leanh::lean_obj_tag(v___x_2311_) == 0 {
                    v_a_2312_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                    crate::leanh::lean_inc(v_a_2312_);
                    crate::leanh::lean_dec_ref_known(v___x_2311_, 1);
                    v___x_2313_ = l_Lean_Expr_headBeta(v_type_2302_);
                    v___x_2314_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_2313_,
                        v_a_2312_,
                        v___y_2306_,
                        v___y_2307_,
                        v___y_2308_,
                        v___y_2309_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2314_) == 0 {
                        v_a_2315_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
                        crate::leanh::lean_inc_n(v_a_2315_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2314_, 1);
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
                        if crate::leanh::lean_obj_tag(v___x_2318_) == 0 {
                            v_a_2319_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                            crate::leanh::lean_inc(v_a_2319_);
                            crate::leanh::lean_dec_ref_known(v___x_2318_, 1);
                            v___x_1533__overap_2320_ = l_Lean_MVarId_assign___redArg(
                                v___x_2305_,
                                v_mvarId_2301_,
                                v_a_2319_,
                            );
                            v___x_2321_ = crate::leanh::lean_apply_5(
                                v___x_1533__overap_2320_,
                                v___y_2306_,
                                v___y_2307_,
                                v___y_2308_,
                                v___y_2309_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_2321_) == 0 {
                                v_isSharedCheck_2330_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2321_)) as u8;
                                if v_isSharedCheck_2330_ == 0 {
                                    v_unused_2331_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                                    crate::leanh::lean_dec(v_unused_2331_);
                                    v___x_2323_ = v___x_2321_;
                                    v_isShared_2324_ = v_isSharedCheck_2330_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2321_);
                                    v___x_2323_ = crate::leanh::lean_box(0);
                                    v_isShared_2324_ = v_isSharedCheck_2330_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2315_);
                                crate::leanh::lean_dec_ref(v_fvars_2303_);
                                v_a_2332_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                                v_isSharedCheck_2339_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2321_)) as u8;
                                if v_isSharedCheck_2339_ == 0 {
                                    v___x_2334_ = v___x_2321_;
                                    v_isShared_2335_ = v_isSharedCheck_2339_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2332_);
                                    crate::leanh::lean_dec(v___x_2321_);
                                    v___x_2334_ = crate::leanh::lean_box(0);
                                    v_isShared_2335_ = v_isSharedCheck_2339_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2315_);
                            crate::leanh::lean_dec(v___y_2309_);
                            crate::leanh::lean_dec_ref(v___y_2308_);
                            crate::leanh::lean_dec(v___y_2307_);
                            crate::leanh::lean_dec_ref(v___y_2306_);
                            crate::leanh::lean_dec_ref(v___x_2305_);
                            crate::leanh::lean_dec_ref(v_fvars_2303_);
                            crate::leanh::lean_dec(v_mvarId_2301_);
                            v_a_2340_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                            v_isSharedCheck_2347_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2318_)) as u8;
                            if v_isSharedCheck_2347_ == 0 {
                                v___x_2342_ = v___x_2318_;
                                v_isShared_2343_ = v_isSharedCheck_2347_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2340_);
                                crate::leanh::lean_dec(v___x_2318_);
                                v___x_2342_ = crate::leanh::lean_box(0);
                                v_isShared_2343_ = v_isSharedCheck_2347_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2309_);
                        crate::leanh::lean_dec_ref(v___y_2308_);
                        crate::leanh::lean_dec(v___y_2307_);
                        crate::leanh::lean_dec_ref(v___y_2306_);
                        crate::leanh::lean_dec_ref(v___x_2305_);
                        crate::leanh::lean_dec_ref(v_fvars_2303_);
                        crate::leanh::lean_dec(v_mvarId_2301_);
                        v_a_2348_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
                        v_isSharedCheck_2355_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2314_)) as u8;
                        if v_isSharedCheck_2355_ == 0 {
                            v___x_2350_ = v___x_2314_;
                            v_isShared_2351_ = v_isSharedCheck_2355_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2348_);
                            crate::leanh::lean_dec(v___x_2314_);
                            v___x_2350_ = crate::leanh::lean_box(0);
                            v_isShared_2351_ = v_isSharedCheck_2355_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2309_);
                    crate::leanh::lean_dec_ref(v___y_2308_);
                    crate::leanh::lean_dec(v___y_2307_);
                    crate::leanh::lean_dec_ref(v___y_2306_);
                    crate::leanh::lean_dec_ref(v___x_2305_);
                    crate::leanh::lean_dec_ref(v_fvars_2303_);
                    crate::leanh::lean_dec_ref(v_type_2302_);
                    crate::leanh::lean_dec(v_mvarId_2301_);
                    v_a_2356_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2363_ = (!crate::leanh::lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2358_ = v___x_2311_;
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2356_);
                        crate::leanh::lean_dec(v___x_2311_);
                        v___x_2358_ = crate::leanh::lean_box(0);
                        v_isShared_2359_ = v_isSharedCheck_2363_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2325_ = l_Lean_Expr_mvarId_x21(v_a_2315_);
                crate::leanh::lean_dec(v_a_2315_);
                v___x_2326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2326_, 0, v_fvars_2303_);
                crate::leanh::lean_ctor_set(v___x_2326_, 1, v___x_2325_);
                if v_isShared_2324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
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
                    v_reuseFailAlloc_2338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
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
                    v_reuseFailAlloc_2346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
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
                    v_reuseFailAlloc_2354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
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
                    v_reuseFailAlloc_2362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
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
    mut v_mvarId_2364_: *mut crate::leanh::LeanObject,
    mut v_type_2365_: *mut crate::leanh::LeanObject,
    mut v_fvars_2366_: *mut crate::leanh::LeanObject,
    mut v_isZero_2367_: *mut crate::leanh::LeanObject,
    mut v___x_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isZero_boxed_2374_: u8 = 0;
    let mut v_res_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_2374_ = (crate::leanh::lean_unbox(v_isZero_2367_) as u8);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2380_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__2;
    v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
    return v___x_2381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__3);
    v___x_2383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__0);
    v___x_2386_ = l_StateRefT_x27_instMonad___redArg(v___x_2385_);
    return v___x_2386_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_Core_instMonadNameGeneratorCoreM;
    v___x_2393_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__7;
    v___x_2394_ = l_Lean_monadNameGeneratorLift___redArg(v___x_2393_, v___x_2392_);
    return v___x_2394_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__8);
    v___f_2397_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__6;
    v___x_2398_ = l_Lean_monadNameGeneratorLift___redArg(v___f_2397_, v___x_2396_);
    return v___x_2398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed(
    mut v___x_2399_: *mut crate::leanh::LeanObject,
    mut v___x_2400_: *mut crate::leanh::LeanObject,
    mut v_type_2401_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2402_: *mut crate::leanh::LeanObject,
    mut v_n_2403_: *mut crate::leanh::LeanObject,
    mut v_mkName_2404_: *mut crate::leanh::LeanObject,
    mut v_lctx_2405_: *mut crate::leanh::LeanObject,
    mut v_fvars_2406_: *mut crate::leanh::LeanObject,
    mut v___x_2407_: *mut crate::leanh::LeanObject,
    mut v_s_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_n_2403_);
    return v_res_2414_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(
    mut v_mvarId_2415_: *mut crate::leanh::LeanObject,
    mut v_mkName_2416_: *mut crate::leanh::LeanObject,
    mut v_i_2417_: *mut crate::leanh::LeanObject,
    mut v_lctx_2418_: *mut crate::leanh::LeanObject,
    mut v_fvars_2419_: *mut crate::leanh::LeanObject,
    mut v_j_2420_: *mut crate::leanh::LeanObject,
    mut v_s_2421_: *mut crate::leanh::LeanObject,
    mut v_type_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
    mut v_a_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v_toFunctor_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v___f_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2487_: u8 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284__overap_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314__overap_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_a_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_binderName_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2538_: u8 = 0;
    let mut v___x_1363__overap_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: u8 = 0;
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_a_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437__overap_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v_unused_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_unused_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
                v_toApplicative_2429_ = crate::leanh::lean_ctor_get(v___x_2428_, 0);
                v_toFunctor_2430_ = crate::leanh::lean_ctor_get(v_toApplicative_2429_, 0);
                v_toSeq_2431_ = crate::leanh::lean_ctor_get(v_toApplicative_2429_, 2);
                v_toSeqLeft_2432_ = crate::leanh::lean_ctor_get(v_toApplicative_2429_, 3);
                v_toSeqRight_2433_ = crate::leanh::lean_ctor_get(v_toApplicative_2429_, 4);
                v___f_2434_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2;
                v___f_2435_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2430_, 2);
                v___f_2436_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2436_, 0, v_toFunctor_2430_);
                v___f_2437_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2437_, 0, v_toFunctor_2430_);
                v___x_2438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2438_, 0, v___f_2436_);
                crate::leanh::lean_ctor_set(v___x_2438_, 1, v___f_2437_);
                crate::leanh::lean_inc(v_toSeqRight_2433_);
                v___f_2439_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2439_, 0, v_toSeqRight_2433_);
                crate::leanh::lean_inc(v_toSeqLeft_2432_);
                v___f_2440_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2440_, 0, v_toSeqLeft_2432_);
                crate::leanh::lean_inc(v_toSeq_2431_);
                v___f_2441_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2441_, 0, v_toSeq_2431_);
                v___x_2442_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2442_, 0, v___x_2438_);
                crate::leanh::lean_ctor_set(v___x_2442_, 1, v___f_2434_);
                crate::leanh::lean_ctor_set(v___x_2442_, 2, v___f_2441_);
                crate::leanh::lean_ctor_set(v___x_2442_, 3, v___f_2440_);
                crate::leanh::lean_ctor_set(v___x_2442_, 4, v___f_2439_);
                v___x_2443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
                crate::leanh::lean_ctor_set(v___x_2443_, 1, v___f_2435_);
                v___x_2444_ = l_StateRefT_x27_instMonad___redArg(v___x_2443_);
                v___x_2445_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_2445_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2445_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2445_, 2, v___x_2444_);
                v___x_2446_ = l_instMonadControlTOfPure___redArg(v___x_2445_);
                v_toApplicative_2447_ = crate::leanh::lean_ctor_get(v___x_2428_, 0);
                v_toFunctor_2448_ = crate::leanh::lean_ctor_get(v_toApplicative_2447_, 0);
                v_toSeq_2449_ = crate::leanh::lean_ctor_get(v_toApplicative_2447_, 2);
                v_toSeqLeft_2450_ = crate::leanh::lean_ctor_get(v_toApplicative_2447_, 3);
                v_toSeqRight_2451_ = crate::leanh::lean_ctor_get(v_toApplicative_2447_, 4);
                crate::leanh::lean_inc_ref_n(v_toFunctor_2448_, 2);
                v___f_2452_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2452_, 0, v_toFunctor_2448_);
                v___f_2453_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2453_, 0, v_toFunctor_2448_);
                v___x_2454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2454_, 0, v___f_2452_);
                crate::leanh::lean_ctor_set(v___x_2454_, 1, v___f_2453_);
                crate::leanh::lean_inc(v_toSeqRight_2451_);
                v___f_2455_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2455_, 0, v_toSeqRight_2451_);
                crate::leanh::lean_inc(v_toSeqLeft_2450_);
                v___f_2456_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2456_, 0, v_toSeqLeft_2450_);
                crate::leanh::lean_inc(v_toSeq_2449_);
                v___f_2457_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2457_, 0, v_toSeq_2449_);
                v___x_2458_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2458_, 0, v___x_2454_);
                crate::leanh::lean_ctor_set(v___x_2458_, 1, v___f_2434_);
                crate::leanh::lean_ctor_set(v___x_2458_, 2, v___f_2457_);
                crate::leanh::lean_ctor_set(v___x_2458_, 3, v___f_2456_);
                crate::leanh::lean_ctor_set(v___x_2458_, 4, v___f_2455_);
                v___x_2459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2459_, 0, v___x_2458_);
                crate::leanh::lean_ctor_set(v___x_2459_, 1, v___f_2435_);
                v___x_2460_ = l_StateRefT_x27_instMonad___redArg(v___x_2459_);
                v_toApplicative_2461_ = crate::leanh::lean_ctor_get(v___x_2460_, 0);
                v_isSharedCheck_2582_ = (!crate::leanh::lean_is_exclusive(v___x_2460_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v_unused_2583_ = crate::leanh::lean_ctor_get(v___x_2460_, 1);
                    crate::leanh::lean_dec(v_unused_2583_);
                    v___x_2463_ = v___x_2460_;
                    v_isShared_2464_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2461_);
                    crate::leanh::lean_dec(v___x_2460_);
                    v___x_2463_ = crate::leanh::lean_box(0);
                    v_isShared_2464_ = v_isSharedCheck_2582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2465_ = crate::leanh::lean_ctor_get(v_toApplicative_2461_, 0);
                v_toSeq_2466_ = crate::leanh::lean_ctor_get(v_toApplicative_2461_, 2);
                v_toSeqLeft_2467_ = crate::leanh::lean_ctor_get(v_toApplicative_2461_, 3);
                v_toSeqRight_2468_ = crate::leanh::lean_ctor_get(v_toApplicative_2461_, 4);
                v_isSharedCheck_2580_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2461_)) as u8;
                if v_isSharedCheck_2580_ == 0 {
                    v_unused_2581_ = crate::leanh::lean_ctor_get(v_toApplicative_2461_, 1);
                    crate::leanh::lean_dec(v_unused_2581_);
                    v___x_2470_ = v_toApplicative_2461_;
                    v_isShared_2471_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2468_);
                    crate::leanh::lean_inc(v_toSeqLeft_2467_);
                    crate::leanh::lean_inc(v_toSeq_2466_);
                    crate::leanh::lean_inc(v_toFunctor_2465_);
                    crate::leanh::lean_dec(v_toApplicative_2461_);
                    v___x_2470_ = crate::leanh::lean_box(0);
                    v_isShared_2471_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2472_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__4;
                v___f_2473_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_2465_);
                v___f_2474_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2474_, 0, v_toFunctor_2465_);
                v___f_2475_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2475_, 0, v_toFunctor_2465_);
                v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2476_, 0, v___f_2474_);
                crate::leanh::lean_ctor_set(v___x_2476_, 1, v___f_2475_);
                v___f_2477_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2477_, 0, v_toSeqRight_2468_);
                v___f_2478_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2478_, 0, v_toSeqLeft_2467_);
                v___f_2479_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2479_, 0, v_toSeq_2466_);
                if v_isShared_2471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2470_, 4, v___f_2477_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 3, v___f_2478_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 2, v___f_2479_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 1, v___f_2472_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 0, v___x_2476_);
                    v___x_2481_ = v___x_2470_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___f_2472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 2, v___f_2479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 3, v___f_2478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 4, v___f_2477_);
                    v___x_2481_ = v_reuseFailAlloc_2579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2463_, 1, v___f_2473_);
                    crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2481_);
                    v___x_2483_ = v___x_2463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___f_2473_);
                    v___x_2483_ = v_reuseFailAlloc_2578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2484_ = l_Lean_Meta_instMonadMCtxMetaM;
                v___x_2485_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__9);
                v_zero_2486_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2487_ = lean_nat_dec_eq(v_i_2417_, v_zero_2486_);
                if v_isZero_2487_ == 1 {
                    crate::leanh::lean_dec(v_s_2421_);
                    crate::leanh::lean_dec(v_i_2417_);
                    crate::leanh::lean_dec_ref(v_mkName_2416_);
                    v___x_2488_ = lean_array_get_size(v_fvars_2419_);
                    v_type_2489_ = lean_expr_instantiate_rev_range(
                        v_type_2422_,
                        v_j_2420_,
                        v___x_2488_,
                        v_fvars_2419_,
                    );
                    crate::leanh::lean_dec_ref(v_type_2422_);
                    v___x_2490_ = crate::leanh::lean_box((v_isZero_2487_) as usize);
                    crate::leanh::lean_inc_ref(v_fvars_2419_);
                    v___f_2491_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                    crate::leanh::lean_closure_set(v___f_2491_, 0, v_mvarId_2415_);
                    crate::leanh::lean_closure_set(v___f_2491_, 1, v_type_2489_);
                    crate::leanh::lean_closure_set(v___f_2491_, 2, v_fvars_2419_);
                    crate::leanh::lean_closure_set(v___f_2491_, 3, v___x_2490_);
                    crate::leanh::lean_closure_set(v___f_2491_, 4, v___x_2484_);
                    crate::leanh::lean_inc_ref(v___x_2483_);
                    crate::leanh::lean_inc_ref(v___x_2446_);
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
                    crate::leanh::lean_inc(v_a_2426_);
                    crate::leanh::lean_inc_ref(v_a_2425_);
                    crate::leanh::lean_inc(v_a_2424_);
                    crate::leanh::lean_inc_ref(v_a_2423_);
                    v___x_2494_ = crate::leanh::lean_apply_5(
                        v___x_1284__overap_2493_,
                        v_a_2423_,
                        v_a_2424_,
                        v_a_2425_,
                        v_a_2426_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2494_;
                } else {
                    v_one_2495_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2496_ = lean_nat_sub(v_i_2417_, v_one_2495_);
                    crate::leanh::lean_dec(v_i_2417_);
                    match crate::leanh::lean_obj_tag(v_type_2422_) {
                        8 => {
                            crate::leanh::lean_dec_ref(v___x_2446_);
                            v_declName_2497_ = crate::leanh::lean_ctor_get(v_type_2422_, 0);
                            crate::leanh::lean_inc(v_declName_2497_);
                            v_type_2498_ = crate::leanh::lean_ctor_get(v_type_2422_, 1);
                            crate::leanh::lean_inc_ref(v_type_2498_);
                            v_value_2499_ = crate::leanh::lean_ctor_get(v_type_2422_, 2);
                            crate::leanh::lean_inc_ref(v_value_2499_);
                            v_body_2500_ = crate::leanh::lean_ctor_get(v_type_2422_, 3);
                            crate::leanh::lean_inc_ref(v_body_2500_);
                            crate::leanh::lean_dec_ref_known(v_type_2422_, 4);
                            v___x_1314__overap_2501_ =
                                l_Lean_mkFreshFVarId___redArg(v___x_2483_, v___x_2485_);
                            crate::leanh::lean_inc(v_a_2426_);
                            crate::leanh::lean_inc_ref(v_a_2425_);
                            crate::leanh::lean_inc(v_a_2424_);
                            crate::leanh::lean_inc_ref(v_a_2423_);
                            v___x_2502_ = crate::leanh::lean_apply_5(
                                v___x_1314__overap_2501_,
                                v_a_2423_,
                                v_a_2424_,
                                v_a_2425_,
                                v_a_2426_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_2502_) == 0 {
                                v_a_2503_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                                crate::leanh::lean_inc(v_a_2503_);
                                crate::leanh::lean_dec_ref_known(v___x_2502_, 1);
                                v___x_2504_ = 1;
                                v___x_2505_ = crate::leanh::lean_box((v___x_2504_) as usize);
                                crate::leanh::lean_inc_ref(v_mkName_2416_);
                                crate::leanh::lean_inc(v_a_2426_);
                                crate::leanh::lean_inc_ref(v_a_2425_);
                                crate::leanh::lean_inc(v_a_2424_);
                                crate::leanh::lean_inc_ref(v_a_2423_);
                                crate::leanh::lean_inc_ref(v_lctx_2418_);
                                v___x_2506_ = crate::leanh::lean_apply_9(
                                    v_mkName_2416_,
                                    v_lctx_2418_,
                                    v_declName_2497_,
                                    v___x_2505_,
                                    v_s_2421_,
                                    v_a_2423_,
                                    v_a_2424_,
                                    v_a_2425_,
                                    v_a_2426_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_2506_) == 0 {
                                    v_a_2507_ = crate::leanh::lean_ctor_get(v___x_2506_, 0);
                                    crate::leanh::lean_inc(v_a_2507_);
                                    crate::leanh::lean_dec_ref_known(v___x_2506_, 1);
                                    v_fst_2508_ = crate::leanh::lean_ctor_get(v_a_2507_, 0);
                                    crate::leanh::lean_inc(v_fst_2508_);
                                    v_snd_2509_ = crate::leanh::lean_ctor_get(v_a_2507_, 1);
                                    crate::leanh::lean_inc(v_snd_2509_);
                                    crate::leanh::lean_dec(v_a_2507_);
                                    v___x_2510_ = lean_array_get_size(v_fvars_2419_);
                                    v_type_2511_ = lean_expr_instantiate_rev_range(
                                        v_type_2498_,
                                        v_j_2420_,
                                        v___x_2510_,
                                        v_fvars_2419_,
                                    );
                                    crate::leanh::lean_dec_ref(v_type_2498_);
                                    v_type_2512_ = l_Lean_Expr_headBeta(v_type_2511_);
                                    v_val_2513_ = lean_expr_instantiate_rev_range(
                                        v_value_2499_,
                                        v_j_2420_,
                                        v___x_2510_,
                                        v_fvars_2419_,
                                    );
                                    crate::leanh::lean_dec_ref(v_value_2499_);
                                    v___x_2514_ = 0;
                                    crate::leanh::lean_inc(v_a_2503_);
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
                                    crate::leanh::lean_dec(v_a_2503_);
                                    crate::leanh::lean_dec_ref(v_body_2500_);
                                    crate::leanh::lean_dec_ref(v_value_2499_);
                                    crate::leanh::lean_dec_ref(v_type_2498_);
                                    crate::leanh::lean_dec(v_n_2496_);
                                    crate::leanh::lean_dec(v_j_2420_);
                                    crate::leanh::lean_dec_ref(v_fvars_2419_);
                                    crate::leanh::lean_dec_ref(v_lctx_2418_);
                                    crate::leanh::lean_dec_ref(v_mkName_2416_);
                                    crate::leanh::lean_dec(v_mvarId_2415_);
                                    v_a_2519_ = crate::leanh::lean_ctor_get(v___x_2506_, 0);
                                    v_isSharedCheck_2526_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2506_)) as u8;
                                    if v_isSharedCheck_2526_ == 0 {
                                        v___x_2521_ = v___x_2506_;
                                        v_isShared_2522_ = v_isSharedCheck_2526_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2519_);
                                        crate::leanh::lean_dec(v___x_2506_);
                                        v___x_2521_ = crate::leanh::lean_box(0);
                                        v_isShared_2522_ = v_isSharedCheck_2526_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_2500_);
                                crate::leanh::lean_dec_ref(v_value_2499_);
                                crate::leanh::lean_dec_ref(v_type_2498_);
                                crate::leanh::lean_dec(v_declName_2497_);
                                crate::leanh::lean_dec(v_n_2496_);
                                crate::leanh::lean_dec(v_s_2421_);
                                crate::leanh::lean_dec(v_j_2420_);
                                crate::leanh::lean_dec_ref(v_fvars_2419_);
                                crate::leanh::lean_dec_ref(v_lctx_2418_);
                                crate::leanh::lean_dec_ref(v_mkName_2416_);
                                crate::leanh::lean_dec(v_mvarId_2415_);
                                v_a_2527_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                                v_isSharedCheck_2534_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2502_)) as u8;
                                if v_isSharedCheck_2534_ == 0 {
                                    v___x_2529_ = v___x_2502_;
                                    v_isShared_2530_ = v_isSharedCheck_2534_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2527_);
                                    crate::leanh::lean_dec(v___x_2502_);
                                    v___x_2529_ = crate::leanh::lean_box(0);
                                    v_isShared_2530_ = v_isSharedCheck_2534_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        7 => {
                            crate::leanh::lean_dec_ref(v___x_2446_);
                            v_binderName_2535_ = crate::leanh::lean_ctor_get(v_type_2422_, 0);
                            crate::leanh::lean_inc(v_binderName_2535_);
                            v_binderType_2536_ = crate::leanh::lean_ctor_get(v_type_2422_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_2536_);
                            v_body_2537_ = crate::leanh::lean_ctor_get(v_type_2422_, 2);
                            crate::leanh::lean_inc_ref(v_body_2537_);
                            v_binderInfo_2538_ = crate::leanh::lean_ctor_get_uint8(
                                v_type_2422_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_type_2422_, 3);
                            v___x_1363__overap_2539_ =
                                l_Lean_mkFreshFVarId___redArg(v___x_2483_, v___x_2485_);
                            crate::leanh::lean_inc(v_a_2426_);
                            crate::leanh::lean_inc_ref(v_a_2425_);
                            crate::leanh::lean_inc(v_a_2424_);
                            crate::leanh::lean_inc_ref(v_a_2423_);
                            v___x_2540_ = crate::leanh::lean_apply_5(
                                v___x_1363__overap_2539_,
                                v_a_2423_,
                                v_a_2424_,
                                v_a_2425_,
                                v_a_2426_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_2540_) == 0 {
                                v_a_2541_ = crate::leanh::lean_ctor_get(v___x_2540_, 0);
                                crate::leanh::lean_inc(v_a_2541_);
                                crate::leanh::lean_dec_ref_known(v___x_2540_, 1);
                                v___x_2542_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2538_);
                                v___x_2543_ = crate::leanh::lean_box((v___x_2542_) as usize);
                                crate::leanh::lean_inc_ref(v_mkName_2416_);
                                crate::leanh::lean_inc(v_a_2426_);
                                crate::leanh::lean_inc_ref(v_a_2425_);
                                crate::leanh::lean_inc(v_a_2424_);
                                crate::leanh::lean_inc_ref(v_a_2423_);
                                crate::leanh::lean_inc_ref(v_lctx_2418_);
                                v___x_2544_ = crate::leanh::lean_apply_9(
                                    v_mkName_2416_,
                                    v_lctx_2418_,
                                    v_binderName_2535_,
                                    v___x_2543_,
                                    v_s_2421_,
                                    v_a_2423_,
                                    v_a_2424_,
                                    v_a_2425_,
                                    v_a_2426_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_2544_) == 0 {
                                    v_a_2545_ = crate::leanh::lean_ctor_get(v___x_2544_, 0);
                                    crate::leanh::lean_inc(v_a_2545_);
                                    crate::leanh::lean_dec_ref_known(v___x_2544_, 1);
                                    v_fst_2546_ = crate::leanh::lean_ctor_get(v_a_2545_, 0);
                                    crate::leanh::lean_inc(v_fst_2546_);
                                    v_snd_2547_ = crate::leanh::lean_ctor_get(v_a_2545_, 1);
                                    crate::leanh::lean_inc(v_snd_2547_);
                                    crate::leanh::lean_dec(v_a_2545_);
                                    v___x_2548_ = lean_array_get_size(v_fvars_2419_);
                                    v_type_2549_ = lean_expr_instantiate_rev_range(
                                        v_binderType_2536_,
                                        v_j_2420_,
                                        v___x_2548_,
                                        v_fvars_2419_,
                                    );
                                    crate::leanh::lean_dec_ref(v_binderType_2536_);
                                    v_type_2550_ = l_Lean_Expr_headBeta(v_type_2549_);
                                    v___x_2551_ = 0;
                                    crate::leanh::lean_inc(v_a_2541_);
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
                                    crate::leanh::lean_dec(v_a_2541_);
                                    crate::leanh::lean_dec_ref(v_body_2537_);
                                    crate::leanh::lean_dec_ref(v_binderType_2536_);
                                    crate::leanh::lean_dec(v_n_2496_);
                                    crate::leanh::lean_dec(v_j_2420_);
                                    crate::leanh::lean_dec_ref(v_fvars_2419_);
                                    crate::leanh::lean_dec_ref(v_lctx_2418_);
                                    crate::leanh::lean_dec_ref(v_mkName_2416_);
                                    crate::leanh::lean_dec(v_mvarId_2415_);
                                    v_a_2556_ = crate::leanh::lean_ctor_get(v___x_2544_, 0);
                                    v_isSharedCheck_2563_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2544_)) as u8;
                                    if v_isSharedCheck_2563_ == 0 {
                                        v___x_2558_ = v___x_2544_;
                                        v_isShared_2559_ = v_isSharedCheck_2563_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2556_);
                                        crate::leanh::lean_dec(v___x_2544_);
                                        v___x_2558_ = crate::leanh::lean_box(0);
                                        v_isShared_2559_ = v_isSharedCheck_2563_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_2537_);
                                crate::leanh::lean_dec_ref(v_binderType_2536_);
                                crate::leanh::lean_dec(v_binderName_2535_);
                                crate::leanh::lean_dec(v_n_2496_);
                                crate::leanh::lean_dec(v_s_2421_);
                                crate::leanh::lean_dec(v_j_2420_);
                                crate::leanh::lean_dec_ref(v_fvars_2419_);
                                crate::leanh::lean_dec_ref(v_lctx_2418_);
                                crate::leanh::lean_dec_ref(v_mkName_2416_);
                                crate::leanh::lean_dec(v_mvarId_2415_);
                                v_a_2564_ = crate::leanh::lean_ctor_get(v___x_2540_, 0);
                                v_isSharedCheck_2571_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2540_)) as u8;
                                if v_isSharedCheck_2571_ == 0 {
                                    v___x_2566_ = v___x_2540_;
                                    v_isShared_2567_ = v_isSharedCheck_2571_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2564_);
                                    crate::leanh::lean_dec(v___x_2540_);
                                    v___x_2566_ = crate::leanh::lean_box(0);
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
                            crate::leanh::lean_dec_ref(v_type_2422_);
                            crate::leanh::lean_inc_ref(v_fvars_2419_);
                            crate::leanh::lean_inc_ref(v_lctx_2418_);
                            crate::leanh::lean_inc_ref_n(v___x_2483_, 2);
                            v___f_2574_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___boxed as *mut core::ffi::c_void, 15, 10);
                            crate::leanh::lean_closure_set(v___f_2574_, 0, v___x_2483_);
                            crate::leanh::lean_closure_set(v___f_2574_, 1, v___x_2484_);
                            crate::leanh::lean_closure_set(v___f_2574_, 2, v_type_2573_);
                            crate::leanh::lean_closure_set(v___f_2574_, 3, v_mvarId_2415_);
                            crate::leanh::lean_closure_set(v___f_2574_, 4, v_n_2496_);
                            crate::leanh::lean_closure_set(v___f_2574_, 5, v_mkName_2416_);
                            crate::leanh::lean_closure_set(v___f_2574_, 6, v_lctx_2418_);
                            crate::leanh::lean_closure_set(v___f_2574_, 7, v_fvars_2419_);
                            crate::leanh::lean_closure_set(v___f_2574_, 8, v___x_2572_);
                            crate::leanh::lean_closure_set(v___f_2574_, 9, v_s_2421_);
                            crate::leanh::lean_inc_ref(v___x_2446_);
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
                            crate::leanh::lean_inc(v_a_2426_);
                            crate::leanh::lean_inc_ref(v_a_2425_);
                            crate::leanh::lean_inc(v_a_2424_);
                            crate::leanh::lean_inc_ref(v_a_2423_);
                            v___x_2577_ = crate::leanh::lean_apply_5(
                                v___x_1437__overap_2576_,
                                v_a_2423_,
                                v_a_2424_,
                                v_a_2425_,
                                v_a_2426_,
                                crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_2525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
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
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
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
                    v_reuseFailAlloc_2562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
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
                    v_reuseFailAlloc_2570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
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
    mut v___x_2584_: *mut crate::leanh::LeanObject,
    mut v___x_2585_: *mut crate::leanh::LeanObject,
    mut v_type_2586_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2587_: *mut crate::leanh::LeanObject,
    mut v_n_2588_: *mut crate::leanh::LeanObject,
    mut v_mkName_2589_: *mut crate::leanh::LeanObject,
    mut v_lctx_2590_: *mut crate::leanh::LeanObject,
    mut v_fvars_2591_: *mut crate::leanh::LeanObject,
    mut v___x_2592_: *mut crate::leanh::LeanObject,
    mut v_s_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1560__overap_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: u8 = 0;
    let mut v___x_2626_: u8 = 0;
    let mut v_a_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1560__overap_2599_ =
                    l_Lean_instantiateMVars___redArg(v___x_2584_, v___x_2585_, v_type_2586_);
                crate::leanh::lean_inc(v___y_2597_);
                crate::leanh::lean_inc_ref(v___y_2596_);
                crate::leanh::lean_inc(v___y_2595_);
                crate::leanh::lean_inc_ref(v___y_2594_);
                v___x_2600_ = crate::leanh::lean_apply_5(
                    v___x_1560__overap_2599_,
                    v___y_2594_,
                    v___y_2595_,
                    v___y_2596_,
                    v___y_2597_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2600_) == 0 {
                    v_a_2601_ = crate::leanh::lean_ctor_get(v___x_2600_, 0);
                    crate::leanh::lean_inc(v_a_2601_);
                    crate::leanh::lean_dec_ref_known(v___x_2600_, 1);
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
                    crate::leanh::lean_dec(v___y_2597_);
                    crate::leanh::lean_dec_ref(v___y_2596_);
                    crate::leanh::lean_dec(v___y_2595_);
                    crate::leanh::lean_dec_ref(v___y_2594_);
                    crate::leanh::lean_dec(v_s_2593_);
                    crate::leanh::lean_dec(v___x_2592_);
                    crate::leanh::lean_dec_ref(v_fvars_2591_);
                    crate::leanh::lean_dec_ref(v_lctx_2590_);
                    crate::leanh::lean_dec_ref(v_mkName_2589_);
                    crate::leanh::lean_dec(v_mvarId_2587_);
                    v_a_2627_ = crate::leanh::lean_ctor_get(v___x_2600_, 0);
                    v_isSharedCheck_2634_ = (!crate::leanh::lean_is_exclusive(v___x_2600_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2629_ = v___x_2600_;
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2627_);
                        crate::leanh::lean_dec(v___x_2600_);
                        v___x_2629_ = crate::leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2634_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2604_ == 0 {
                    crate::leanh::lean_inc(v___y_2597_);
                    crate::leanh::lean_inc_ref(v___y_2596_);
                    crate::leanh::lean_inc(v___y_2595_);
                    crate::leanh::lean_inc_ref(v___y_2594_);
                    v___x_2605_ = lean_whnf(
                        v___x_2602_,
                        v___y_2594_,
                        v___y_2595_,
                        v___y_2596_,
                        v___y_2597_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2605_) == 0 {
                        v_a_2606_ = crate::leanh::lean_ctor_get(v___x_2605_, 0);
                        crate::leanh::lean_inc(v_a_2606_);
                        crate::leanh::lean_dec_ref_known(v___x_2605_, 1);
                        v___x_2607_ = l_Lean_Expr_isForall(v_a_2606_);
                        if v___x_2607_ == 0 {
                            crate::leanh::lean_dec(v_a_2606_);
                            crate::leanh::lean_dec(v_s_2593_);
                            crate::leanh::lean_dec(v___x_2592_);
                            crate::leanh::lean_dec_ref(v_fvars_2591_);
                            crate::leanh::lean_dec_ref(v_lctx_2590_);
                            crate::leanh::lean_dec_ref(v_mkName_2589_);
                            v___x_2608_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                            v___x_2609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
                            v___x_2610_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_2608_,
                                v_mvarId_2587_,
                                v___x_2609_,
                                v___y_2594_,
                                v___y_2595_,
                                v___y_2596_,
                                v___y_2597_,
                            );
                            crate::leanh::lean_dec(v___y_2597_);
                            crate::leanh::lean_dec_ref(v___y_2596_);
                            crate::leanh::lean_dec(v___y_2595_);
                            crate::leanh::lean_dec_ref(v___y_2594_);
                            return v___x_2610_;
                        } else {
                            v___x_2611_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2612_ = lean_nat_add(v_n_2588_, v___x_2611_);
                            v___x_2613_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg(v_mvarId_2587_, v_mkName_2589_, v___x_2612_, v_lctx_2590_, v_fvars_2591_, v___x_2592_, v_s_2593_, v_a_2606_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
                            crate::leanh::lean_dec(v___y_2597_);
                            crate::leanh::lean_dec_ref(v___y_2596_);
                            crate::leanh::lean_dec(v___y_2595_);
                            crate::leanh::lean_dec_ref(v___y_2594_);
                            return v___x_2613_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2597_);
                        crate::leanh::lean_dec_ref(v___y_2596_);
                        crate::leanh::lean_dec(v___y_2595_);
                        crate::leanh::lean_dec_ref(v___y_2594_);
                        crate::leanh::lean_dec(v_s_2593_);
                        crate::leanh::lean_dec(v___x_2592_);
                        crate::leanh::lean_dec_ref(v_fvars_2591_);
                        crate::leanh::lean_dec_ref(v_lctx_2590_);
                        crate::leanh::lean_dec_ref(v_mkName_2589_);
                        crate::leanh::lean_dec(v_mvarId_2587_);
                        v_a_2614_ = crate::leanh::lean_ctor_get(v___x_2605_, 0);
                        v_isSharedCheck_2621_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2605_)) as u8;
                        if v_isSharedCheck_2621_ == 0 {
                            v___x_2616_ = v___x_2605_;
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2614_);
                            crate::leanh::lean_dec(v___x_2605_);
                            v___x_2616_ = crate::leanh::lean_box(0);
                            v_isShared_2617_ = v_isSharedCheck_2621_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2622_ = crate::leanh::lean_unsigned_to_nat(1);
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
                    crate::leanh::lean_dec(v___y_2597_);
                    crate::leanh::lean_dec_ref(v___y_2596_);
                    crate::leanh::lean_dec(v___y_2595_);
                    crate::leanh::lean_dec_ref(v___y_2594_);
                    return v___x_2624_;
                }
            }
            2 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
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
                    v_reuseFailAlloc_2633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
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
    mut v_mvarId_2635_: *mut crate::leanh::LeanObject,
    mut v_mkName_2636_: *mut crate::leanh::LeanObject,
    mut v_i_2637_: *mut crate::leanh::LeanObject,
    mut v_lctx_2638_: *mut crate::leanh::LeanObject,
    mut v_fvars_2639_: *mut crate::leanh::LeanObject,
    mut v_j_2640_: *mut crate::leanh::LeanObject,
    mut v_s_2641_: *mut crate::leanh::LeanObject,
    mut v_type_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2646_);
    crate::leanh::lean_dec_ref(v_a_2645_);
    crate::leanh::lean_dec(v_a_2644_);
    crate::leanh::lean_dec_ref(v_a_2643_);
    return v_res_2648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop(
    mut v_00_u03c3_2649_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2650_: *mut crate::leanh::LeanObject,
    mut v_mkName_2651_: *mut crate::leanh::LeanObject,
    mut v_i_2652_: *mut crate::leanh::LeanObject,
    mut v_lctx_2653_: *mut crate::leanh::LeanObject,
    mut v_fvars_2654_: *mut crate::leanh::LeanObject,
    mut v_j_2655_: *mut crate::leanh::LeanObject,
    mut v_s_2656_: *mut crate::leanh::LeanObject,
    mut v_type_2657_: *mut crate::leanh::LeanObject,
    mut v_a_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03c3_2664_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2665_: *mut crate::leanh::LeanObject,
    mut v_mkName_2666_: *mut crate::leanh::LeanObject,
    mut v_i_2667_: *mut crate::leanh::LeanObject,
    mut v_lctx_2668_: *mut crate::leanh::LeanObject,
    mut v_fvars_2669_: *mut crate::leanh::LeanObject,
    mut v_j_2670_: *mut crate::leanh::LeanObject,
    mut v_s_2671_: *mut crate::leanh::LeanObject,
    mut v_type_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
    mut v_a_2676_: *mut crate::leanh::LeanObject,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2676_);
    crate::leanh::lean_dec_ref(v_a_2675_);
    crate::leanh::lean_dec(v_a_2674_);
    crate::leanh::lean_dec_ref(v_a_2673_);
    return v_res_2678_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0(
    mut v_mvarId_2700_: *mut crate::leanh::LeanObject,
    mut v___x_2701_: *mut crate::leanh::LeanObject,
    mut v_mkName_2702_: *mut crate::leanh::LeanObject,
    mut v_n_2703_: *mut crate::leanh::LeanObject,
    mut v_s_2704_: *mut crate::leanh::LeanObject,
    mut v___f_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v_fst_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2728_: usize = 0;
    let mut v___x_2729_: usize = 0;
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_a_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2754_: u8 = 0;
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2700_);
                v___x_2711_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2700_,
                    v___x_2701_,
                    v___y_2706_,
                    v___y_2707_,
                    v___y_2708_,
                    v___y_2709_,
                );
                if crate::leanh::lean_obj_tag(v___x_2711_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2711_, 1);
                    crate::leanh::lean_inc(v_mvarId_2700_);
                    v___x_2712_ = l_Lean_MVarId_getType(
                        v_mvarId_2700_,
                        v___y_2706_,
                        v___y_2707_,
                        v___y_2708_,
                        v___y_2709_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2712_) == 0 {
                        v_a_2713_ = crate::leanh::lean_ctor_get(v___x_2712_, 0);
                        crate::leanh::lean_inc(v_a_2713_);
                        crate::leanh::lean_dec_ref_known(v___x_2712_, 1);
                        v_lctx_2714_ = crate::leanh::lean_ctor_get(v___y_2706_, 2);
                        crate::leanh::lean_inc_ref(v_lctx_2714_);
                        v___x_2715_ = crate::leanh::lean_unsigned_to_nat(0);
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
                        crate::leanh::lean_dec_ref(v___y_2706_);
                        if crate::leanh::lean_obj_tag(v___x_2717_) == 0 {
                            v_a_2718_ = crate::leanh::lean_ctor_get(v___x_2717_, 0);
                            v_isSharedCheck_2738_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2717_)) as u8;
                            if v_isSharedCheck_2738_ == 0 {
                                v___x_2720_ = v___x_2717_;
                                v_isShared_2721_ = v_isSharedCheck_2738_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2718_);
                                crate::leanh::lean_dec(v___x_2717_);
                                v___x_2720_ = crate::leanh::lean_box(0);
                                v_isShared_2721_ = v_isSharedCheck_2738_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___f_2705_);
                            v_a_2739_ = crate::leanh::lean_ctor_get(v___x_2717_, 0);
                            v_isSharedCheck_2746_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2717_)) as u8;
                            if v_isSharedCheck_2746_ == 0 {
                                v___x_2741_ = v___x_2717_;
                                v_isShared_2742_ = v_isSharedCheck_2746_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2739_);
                                crate::leanh::lean_dec(v___x_2717_);
                                v___x_2741_ = crate::leanh::lean_box(0);
                                v_isShared_2742_ = v_isSharedCheck_2746_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2706_);
                        crate::leanh::lean_dec_ref(v___f_2705_);
                        crate::leanh::lean_dec(v_s_2704_);
                        crate::leanh::lean_dec(v_n_2703_);
                        crate::leanh::lean_dec_ref(v_mkName_2702_);
                        crate::leanh::lean_dec(v_mvarId_2700_);
                        v_a_2747_ = crate::leanh::lean_ctor_get(v___x_2712_, 0);
                        v_isSharedCheck_2754_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2712_)) as u8;
                        if v_isSharedCheck_2754_ == 0 {
                            v___x_2749_ = v___x_2712_;
                            v_isShared_2750_ = v_isSharedCheck_2754_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2747_);
                            crate::leanh::lean_dec(v___x_2712_);
                            v___x_2749_ = crate::leanh::lean_box(0);
                            v_isShared_2750_ = v_isSharedCheck_2754_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2706_);
                    crate::leanh::lean_dec_ref(v___f_2705_);
                    crate::leanh::lean_dec(v_s_2704_);
                    crate::leanh::lean_dec(v_n_2703_);
                    crate::leanh::lean_dec_ref(v_mkName_2702_);
                    crate::leanh::lean_dec(v_mvarId_2700_);
                    v_a_2755_ = crate::leanh::lean_ctor_get(v___x_2711_, 0);
                    v_isSharedCheck_2762_ = (!crate::leanh::lean_is_exclusive(v___x_2711_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v___x_2711_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2755_);
                        crate::leanh::lean_dec(v___x_2711_);
                        v___x_2757_ = crate::leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2722_ = crate::leanh::lean_ctor_get(v_a_2718_, 0);
                v_snd_2723_ = crate::leanh::lean_ctor_get(v_a_2718_, 1);
                v_isSharedCheck_2737_ = (!crate::leanh::lean_is_exclusive(v_a_2718_)) as u8;
                if v_isSharedCheck_2737_ == 0 {
                    v___x_2725_ = v_a_2718_;
                    v_isShared_2726_ = v_isSharedCheck_2737_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2723_);
                    crate::leanh::lean_inc(v_fst_2722_);
                    crate::leanh::lean_dec(v_a_2718_);
                    v___x_2725_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2727_,
                    v___f_2705_,
                    v_sz_2728_,
                    v___x_2729_,
                    v_fst_2722_,
                );
                if v_isShared_2726_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2725_, 0, v___x_2730_);
                    v___x_2732_ = v___x_2725_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_snd_2723_);
                    v___x_2732_ = v_reuseFailAlloc_2736_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2720_, 0, v___x_2732_);
                    v___x_2734_ = v___x_2720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
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
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
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
                    v_reuseFailAlloc_2753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
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
                    v_reuseFailAlloc_2761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
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
    mut v_mvarId_2763_: *mut crate::leanh::LeanObject,
    mut v___x_2764_: *mut crate::leanh::LeanObject,
    mut v_mkName_2765_: *mut crate::leanh::LeanObject,
    mut v_n_2766_: *mut crate::leanh::LeanObject,
    mut v_s_2767_: *mut crate::leanh::LeanObject,
    mut v___f_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
    mut v___y_2771_: *mut crate::leanh::LeanObject,
    mut v___y_2772_: *mut crate::leanh::LeanObject,
    mut v___y_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_2772_);
    crate::leanh::lean_dec_ref(v___y_2771_);
    crate::leanh::lean_dec(v___y_2770_);
    return v_res_2774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg(
    mut v_mvarId_2776_: *mut crate::leanh::LeanObject,
    mut v_n_2777_: *mut crate::leanh::LeanObject,
    mut v_mkName_2778_: *mut crate::leanh::LeanObject,
    mut v_s_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_a_2782_: *mut crate::leanh::LeanObject,
    mut v_a_2783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v_toFunctor_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___f_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43__overap_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_unused_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2785_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
                v_toApplicative_2786_ = crate::leanh::lean_ctor_get(v___x_2785_, 0);
                v_toFunctor_2787_ = crate::leanh::lean_ctor_get(v_toApplicative_2786_, 0);
                v_toSeq_2788_ = crate::leanh::lean_ctor_get(v_toApplicative_2786_, 2);
                v_toSeqLeft_2789_ = crate::leanh::lean_ctor_get(v_toApplicative_2786_, 3);
                v_toSeqRight_2790_ = crate::leanh::lean_ctor_get(v_toApplicative_2786_, 4);
                v___f_2791_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2;
                v___f_2792_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2787_, 2);
                v___f_2793_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2793_, 0, v_toFunctor_2787_);
                v___f_2794_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2794_, 0, v_toFunctor_2787_);
                v___x_2795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2795_, 0, v___f_2793_);
                crate::leanh::lean_ctor_set(v___x_2795_, 1, v___f_2794_);
                crate::leanh::lean_inc(v_toSeqRight_2790_);
                v___f_2796_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2796_, 0, v_toSeqRight_2790_);
                crate::leanh::lean_inc(v_toSeqLeft_2789_);
                v___f_2797_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2797_, 0, v_toSeqLeft_2789_);
                crate::leanh::lean_inc(v_toSeq_2788_);
                v___f_2798_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2798_, 0, v_toSeq_2788_);
                v___x_2799_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2795_);
                crate::leanh::lean_ctor_set(v___x_2799_, 1, v___f_2791_);
                crate::leanh::lean_ctor_set(v___x_2799_, 2, v___f_2798_);
                crate::leanh::lean_ctor_set(v___x_2799_, 3, v___f_2797_);
                crate::leanh::lean_ctor_set(v___x_2799_, 4, v___f_2796_);
                v___x_2800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2800_, 0, v___x_2799_);
                crate::leanh::lean_ctor_set(v___x_2800_, 1, v___f_2792_);
                v___x_2801_ = l_StateRefT_x27_instMonad___redArg(v___x_2800_);
                v___x_2802_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_2802_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2802_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2802_, 2, v___x_2801_);
                v___x_2803_ = l_instMonadControlTOfPure___redArg(v___x_2802_);
                v_toApplicative_2804_ = crate::leanh::lean_ctor_get(v___x_2785_, 0);
                v_toFunctor_2805_ = crate::leanh::lean_ctor_get(v_toApplicative_2804_, 0);
                v_toSeq_2806_ = crate::leanh::lean_ctor_get(v_toApplicative_2804_, 2);
                v_toSeqLeft_2807_ = crate::leanh::lean_ctor_get(v_toApplicative_2804_, 3);
                v_toSeqRight_2808_ = crate::leanh::lean_ctor_get(v_toApplicative_2804_, 4);
                crate::leanh::lean_inc_ref_n(v_toFunctor_2805_, 2);
                v___f_2809_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2809_, 0, v_toFunctor_2805_);
                v___f_2810_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2810_, 0, v_toFunctor_2805_);
                v___x_2811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2811_, 0, v___f_2809_);
                crate::leanh::lean_ctor_set(v___x_2811_, 1, v___f_2810_);
                crate::leanh::lean_inc(v_toSeqRight_2808_);
                v___f_2812_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2812_, 0, v_toSeqRight_2808_);
                crate::leanh::lean_inc(v_toSeqLeft_2807_);
                v___f_2813_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2813_, 0, v_toSeqLeft_2807_);
                crate::leanh::lean_inc(v_toSeq_2806_);
                v___f_2814_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2814_, 0, v_toSeq_2806_);
                v___x_2815_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2815_, 0, v___x_2811_);
                crate::leanh::lean_ctor_set(v___x_2815_, 1, v___f_2791_);
                crate::leanh::lean_ctor_set(v___x_2815_, 2, v___f_2814_);
                crate::leanh::lean_ctor_set(v___x_2815_, 3, v___f_2813_);
                crate::leanh::lean_ctor_set(v___x_2815_, 4, v___f_2812_);
                v___x_2816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                crate::leanh::lean_ctor_set(v___x_2816_, 1, v___f_2792_);
                v___x_2817_ = l_StateRefT_x27_instMonad___redArg(v___x_2816_);
                v_toApplicative_2818_ = crate::leanh::lean_ctor_get(v___x_2817_, 0);
                v_isSharedCheck_2850_ = (!crate::leanh::lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2850_ == 0 {
                    v_unused_2851_ = crate::leanh::lean_ctor_get(v___x_2817_, 1);
                    crate::leanh::lean_dec(v_unused_2851_);
                    v___x_2820_ = v___x_2817_;
                    v_isShared_2821_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2818_);
                    crate::leanh::lean_dec(v___x_2817_);
                    v___x_2820_ = crate::leanh::lean_box(0);
                    v_isShared_2821_ = v_isSharedCheck_2850_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2822_ = crate::leanh::lean_ctor_get(v_toApplicative_2818_, 0);
                v_toSeq_2823_ = crate::leanh::lean_ctor_get(v_toApplicative_2818_, 2);
                v_toSeqLeft_2824_ = crate::leanh::lean_ctor_get(v_toApplicative_2818_, 3);
                v_toSeqRight_2825_ = crate::leanh::lean_ctor_get(v_toApplicative_2818_, 4);
                v_isSharedCheck_2848_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2818_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v_unused_2849_ = crate::leanh::lean_ctor_get(v_toApplicative_2818_, 1);
                    crate::leanh::lean_dec(v_unused_2849_);
                    v___x_2827_ = v_toApplicative_2818_;
                    v_isShared_2828_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2825_);
                    crate::leanh::lean_inc(v_toSeqLeft_2824_);
                    crate::leanh::lean_inc(v_toSeq_2823_);
                    crate::leanh::lean_inc(v_toFunctor_2822_);
                    crate::leanh::lean_dec(v_toApplicative_2818_);
                    v___x_2827_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc_ref(v_toFunctor_2822_);
                v___f_2832_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2832_, 0, v_toFunctor_2822_);
                v___f_2833_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2833_, 0, v_toFunctor_2822_);
                v___x_2834_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2834_, 0, v___f_2832_);
                crate::leanh::lean_ctor_set(v___x_2834_, 1, v___f_2833_);
                v___f_2835_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2835_, 0, v_toSeqRight_2825_);
                v___f_2836_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2836_, 0, v_toSeqLeft_2824_);
                v___f_2837_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2837_, 0, v_toSeq_2823_);
                if v_isShared_2828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2827_, 4, v___f_2835_);
                    crate::leanh::lean_ctor_set(v___x_2827_, 3, v___f_2836_);
                    crate::leanh::lean_ctor_set(v___x_2827_, 2, v___f_2837_);
                    crate::leanh::lean_ctor_set(v___x_2827_, 1, v___f_2830_);
                    crate::leanh::lean_ctor_set(v___x_2827_, 0, v___x_2834_);
                    v___x_2839_ = v___x_2827_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___f_2830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 2, v___f_2837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 3, v___f_2836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 4, v___f_2835_);
                    v___x_2839_ = v_reuseFailAlloc_2847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2820_, 1, v___f_2831_);
                    crate::leanh::lean_ctor_set(v___x_2820_, 0, v___x_2839_);
                    v___x_2841_ = v___x_2820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___f_2831_);
                    v___x_2841_ = v_reuseFailAlloc_2846_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2842_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                crate::leanh::lean_inc(v_mvarId_2776_);
                v___f_2843_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_2843_, 0, v_mvarId_2776_);
                crate::leanh::lean_closure_set(v___f_2843_, 1, v___x_2842_);
                crate::leanh::lean_closure_set(v___f_2843_, 2, v_mkName_2778_);
                crate::leanh::lean_closure_set(v___f_2843_, 3, v_n_2777_);
                crate::leanh::lean_closure_set(v___f_2843_, 4, v_s_2779_);
                crate::leanh::lean_closure_set(v___f_2843_, 5, v___f_2829_);
                v___x_43__overap_2844_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2803_,
                    v___x_2841_,
                    v_mvarId_2776_,
                    v___f_2843_,
                );
                crate::leanh::lean_inc(v_a_2783_);
                crate::leanh::lean_inc_ref(v_a_2782_);
                crate::leanh::lean_inc(v_a_2781_);
                crate::leanh::lean_inc_ref(v_a_2780_);
                v___x_2845_ = crate::leanh::lean_apply_5(
                    v___x_43__overap_2844_,
                    v_a_2780_,
                    v_a_2781_,
                    v_a_2782_,
                    v_a_2783_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___boxed(
    mut v_mvarId_2852_: *mut crate::leanh::LeanObject,
    mut v_n_2853_: *mut crate::leanh::LeanObject,
    mut v_mkName_2854_: *mut crate::leanh::LeanObject,
    mut v_s_2855_: *mut crate::leanh::LeanObject,
    mut v_a_2856_: *mut crate::leanh::LeanObject,
    mut v_a_2857_: *mut crate::leanh::LeanObject,
    mut v_a_2858_: *mut crate::leanh::LeanObject,
    mut v_a_2859_: *mut crate::leanh::LeanObject,
    mut v_a_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2859_);
    crate::leanh::lean_dec_ref(v_a_2858_);
    crate::leanh::lean_dec(v_a_2857_);
    crate::leanh::lean_dec_ref(v_a_2856_);
    return v_res_2861_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp(
    mut v_00_u03c3_2862_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2863_: *mut crate::leanh::LeanObject,
    mut v_n_2864_: *mut crate::leanh::LeanObject,
    mut v_mkName_2865_: *mut crate::leanh::LeanObject,
    mut v_s_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
    mut v_a_2870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v_toFunctor_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___f_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617__overap_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_unused_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut v_unused_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__1);
                v_toApplicative_2873_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
                v_toFunctor_2874_ = crate::leanh::lean_ctor_get(v_toApplicative_2873_, 0);
                v_toSeq_2875_ = crate::leanh::lean_ctor_get(v_toApplicative_2873_, 2);
                v_toSeqLeft_2876_ = crate::leanh::lean_ctor_get(v_toApplicative_2873_, 3);
                v_toSeqRight_2877_ = crate::leanh::lean_ctor_get(v_toApplicative_2873_, 4);
                v___f_2878_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__2;
                v___f_2879_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2874_, 2);
                v___f_2880_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2880_, 0, v_toFunctor_2874_);
                v___f_2881_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2881_, 0, v_toFunctor_2874_);
                v___x_2882_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2882_, 0, v___f_2880_);
                crate::leanh::lean_ctor_set(v___x_2882_, 1, v___f_2881_);
                crate::leanh::lean_inc(v_toSeqRight_2877_);
                v___f_2883_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2883_, 0, v_toSeqRight_2877_);
                crate::leanh::lean_inc(v_toSeqLeft_2876_);
                v___f_2884_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2884_, 0, v_toSeqLeft_2876_);
                crate::leanh::lean_inc(v_toSeq_2875_);
                v___f_2885_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2885_, 0, v_toSeq_2875_);
                v___x_2886_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2886_, 0, v___x_2882_);
                crate::leanh::lean_ctor_set(v___x_2886_, 1, v___f_2878_);
                crate::leanh::lean_ctor_set(v___x_2886_, 2, v___f_2885_);
                crate::leanh::lean_ctor_set(v___x_2886_, 3, v___f_2884_);
                crate::leanh::lean_ctor_set(v___x_2886_, 4, v___f_2883_);
                v___x_2887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2887_, 0, v___x_2886_);
                crate::leanh::lean_ctor_set(v___x_2887_, 1, v___f_2879_);
                v___x_2888_ = l_StateRefT_x27_instMonad___redArg(v___x_2887_);
                v___x_2889_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_2889_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2889_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2889_, 2, v___x_2888_);
                v___x_2890_ = l_instMonadControlTOfPure___redArg(v___x_2889_);
                v_toApplicative_2891_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
                v_toFunctor_2892_ = crate::leanh::lean_ctor_get(v_toApplicative_2891_, 0);
                v_toSeq_2893_ = crate::leanh::lean_ctor_get(v_toApplicative_2891_, 2);
                v_toSeqLeft_2894_ = crate::leanh::lean_ctor_get(v_toApplicative_2891_, 3);
                v_toSeqRight_2895_ = crate::leanh::lean_ctor_get(v_toApplicative_2891_, 4);
                crate::leanh::lean_inc_ref_n(v_toFunctor_2892_, 2);
                v___f_2896_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2896_, 0, v_toFunctor_2892_);
                v___f_2897_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2897_, 0, v_toFunctor_2892_);
                v___x_2898_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2898_, 0, v___f_2896_);
                crate::leanh::lean_ctor_set(v___x_2898_, 1, v___f_2897_);
                crate::leanh::lean_inc(v_toSeqRight_2895_);
                v___f_2899_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2899_, 0, v_toSeqRight_2895_);
                crate::leanh::lean_inc(v_toSeqLeft_2894_);
                v___f_2900_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2900_, 0, v_toSeqLeft_2894_);
                crate::leanh::lean_inc(v_toSeq_2893_);
                v___f_2901_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2901_, 0, v_toSeq_2893_);
                v___x_2902_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2902_, 0, v___x_2898_);
                crate::leanh::lean_ctor_set(v___x_2902_, 1, v___f_2878_);
                crate::leanh::lean_ctor_set(v___x_2902_, 2, v___f_2901_);
                crate::leanh::lean_ctor_set(v___x_2902_, 3, v___f_2900_);
                crate::leanh::lean_ctor_set(v___x_2902_, 4, v___f_2899_);
                v___x_2903_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2902_);
                crate::leanh::lean_ctor_set(v___x_2903_, 1, v___f_2879_);
                v___x_2904_ = l_StateRefT_x27_instMonad___redArg(v___x_2903_);
                v_toApplicative_2905_ = crate::leanh::lean_ctor_get(v___x_2904_, 0);
                v_isSharedCheck_2937_ = (!crate::leanh::lean_is_exclusive(v___x_2904_)) as u8;
                if v_isSharedCheck_2937_ == 0 {
                    v_unused_2938_ = crate::leanh::lean_ctor_get(v___x_2904_, 1);
                    crate::leanh::lean_dec(v_unused_2938_);
                    v___x_2907_ = v___x_2904_;
                    v_isShared_2908_ = v_isSharedCheck_2937_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2905_);
                    crate::leanh::lean_dec(v___x_2904_);
                    v___x_2907_ = crate::leanh::lean_box(0);
                    v_isShared_2908_ = v_isSharedCheck_2937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2909_ = crate::leanh::lean_ctor_get(v_toApplicative_2905_, 0);
                v_toSeq_2910_ = crate::leanh::lean_ctor_get(v_toApplicative_2905_, 2);
                v_toSeqLeft_2911_ = crate::leanh::lean_ctor_get(v_toApplicative_2905_, 3);
                v_toSeqRight_2912_ = crate::leanh::lean_ctor_get(v_toApplicative_2905_, 4);
                v_isSharedCheck_2935_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2905_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v_unused_2936_ = crate::leanh::lean_ctor_get(v_toApplicative_2905_, 1);
                    crate::leanh::lean_dec(v_unused_2936_);
                    v___x_2914_ = v_toApplicative_2905_;
                    v_isShared_2915_ = v_isSharedCheck_2935_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2912_);
                    crate::leanh::lean_inc(v_toSeqLeft_2911_);
                    crate::leanh::lean_inc(v_toSeq_2910_);
                    crate::leanh::lean_inc(v_toFunctor_2909_);
                    crate::leanh::lean_dec(v_toApplicative_2905_);
                    v___x_2914_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc_ref(v_toFunctor_2909_);
                v___f_2919_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2919_, 0, v_toFunctor_2909_);
                v___f_2920_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2920_, 0, v_toFunctor_2909_);
                v___x_2921_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2921_, 0, v___f_2919_);
                crate::leanh::lean_ctor_set(v___x_2921_, 1, v___f_2920_);
                v___f_2922_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2922_, 0, v_toSeqRight_2912_);
                v___f_2923_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2923_, 0, v_toSeqLeft_2911_);
                v___f_2924_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2924_, 0, v_toSeq_2910_);
                if v_isShared_2915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2914_, 4, v___f_2922_);
                    crate::leanh::lean_ctor_set(v___x_2914_, 3, v___f_2923_);
                    crate::leanh::lean_ctor_set(v___x_2914_, 2, v___f_2924_);
                    crate::leanh::lean_ctor_set(v___x_2914_, 1, v___f_2917_);
                    crate::leanh::lean_ctor_set(v___x_2914_, 0, v___x_2921_);
                    v___x_2926_ = v___x_2914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 1, v___f_2917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 2, v___f_2924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 3, v___f_2923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 4, v___f_2922_);
                    v___x_2926_ = v_reuseFailAlloc_2934_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2907_, 1, v___f_2918_);
                    crate::leanh::lean_ctor_set(v___x_2907_, 0, v___x_2926_);
                    v___x_2928_ = v___x_2907_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___f_2918_);
                    v___x_2928_ = v_reuseFailAlloc_2933_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2929_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                crate::leanh::lean_inc(v_mvarId_2863_);
                v___f_2930_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_2930_, 0, v_mvarId_2863_);
                crate::leanh::lean_closure_set(v___f_2930_, 1, v___x_2929_);
                crate::leanh::lean_closure_set(v___f_2930_, 2, v_mkName_2865_);
                crate::leanh::lean_closure_set(v___f_2930_, 3, v_n_2864_);
                crate::leanh::lean_closure_set(v___f_2930_, 4, v_s_2866_);
                crate::leanh::lean_closure_set(v___f_2930_, 5, v___f_2916_);
                v___x_617__overap_2931_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2890_,
                    v___x_2928_,
                    v_mvarId_2863_,
                    v___f_2930_,
                );
                crate::leanh::lean_inc(v_a_2870_);
                crate::leanh::lean_inc_ref(v_a_2869_);
                crate::leanh::lean_inc(v_a_2868_);
                crate::leanh::lean_inc_ref(v_a_2867_);
                v___x_2932_ = crate::leanh::lean_apply_5(
                    v___x_617__overap_2931_,
                    v_a_2867_,
                    v_a_2868_,
                    v_a_2869_,
                    v_a_2870_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___boxed(
    mut v_00_u03c3_2939_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2940_: *mut crate::leanh::LeanObject,
    mut v_n_2941_: *mut crate::leanh::LeanObject,
    mut v_mkName_2942_: *mut crate::leanh::LeanObject,
    mut v_s_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
    mut v_a_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_2947_);
    crate::leanh::lean_dec_ref(v_a_2946_);
    crate::leanh::lean_dec(v_a_2945_);
    crate::leanh::lean_dec_ref(v_a_2944_);
    return v_res_2949_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(
    mut v_name_2950_: *mut crate::leanh::LeanObject,
    mut v_decl_2951_: *mut crate::leanh::LeanObject,
    mut v_ref_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2954_ = crate::leanh::lean_ctor_get(v_decl_2951_, 0);
                v_descr_2955_ = crate::leanh::lean_ctor_get(v_decl_2951_, 1);
                v_deprecation_x3f_2956_ = crate::leanh::lean_ctor_get(v_decl_2951_, 2);
                v___x_2957_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2958_ = (crate::leanh::lean_unbox(v_defValue_2954_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_2957_, 0 as u32, v___x_2958_);
                crate::leanh::lean_inc(v_deprecation_x3f_2956_);
                crate::leanh::lean_inc_ref(v_descr_2955_);
                crate::leanh::lean_inc_n(v_name_2950_, 2);
                v___x_2959_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2959_, 0, v_name_2950_);
                crate::leanh::lean_ctor_set(v___x_2959_, 1, v_ref_2952_);
                crate::leanh::lean_ctor_set(v___x_2959_, 2, v___x_2957_);
                crate::leanh::lean_ctor_set(v___x_2959_, 3, v_descr_2955_);
                crate::leanh::lean_ctor_set(v___x_2959_, 4, v_deprecation_x3f_2956_);
                v___x_2960_ = lean_register_option(v_name_2950_, v___x_2959_);
                if crate::leanh::lean_obj_tag(v___x_2960_) == 0 {
                    v_isSharedCheck_2968_ = (!crate::leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v_unused_2969_ = crate::leanh::lean_ctor_get(v___x_2960_, 0);
                        crate::leanh::lean_dec(v_unused_2969_);
                        v___x_2962_ = v___x_2960_;
                        v_isShared_2963_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2960_);
                        v___x_2962_ = crate::leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2950_);
                    v_a_2970_ = crate::leanh::lean_ctor_get(v___x_2960_, 0);
                    v_isSharedCheck_2977_ = (!crate::leanh::lean_is_exclusive(v___x_2960_)) as u8;
                    if v_isSharedCheck_2977_ == 0 {
                        v___x_2972_ = v___x_2960_;
                        v_isShared_2973_ = v_isSharedCheck_2977_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2970_);
                        crate::leanh::lean_dec(v___x_2960_);
                        v___x_2972_ = crate::leanh::lean_box(0);
                        v_isShared_2973_ = v_isSharedCheck_2977_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_2954_);
                v___x_2964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2964_, 0, v_name_2950_);
                crate::leanh::lean_ctor_set(v___x_2964_, 1, v_defValue_2954_);
                if v_isShared_2963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2962_, 0, v___x_2964_);
                    v___x_2966_ = v___x_2962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
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
                    v_reuseFailAlloc_2976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
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
    mut v_name_2978_: *mut crate::leanh::LeanObject,
    mut v_decl_2979_: *mut crate::leanh::LeanObject,
    mut v_ref_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v_name_2978_, v_decl_2979_, v_ref_2980_);
    crate::leanh::lean_dec_ref(v_decl_2979_);
    return v_res_2982_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_;
    v___x_3003_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_;
    v___x_3004_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_;
    v___x_3005_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4__spec__0(v___x_3002_, v___x_3003_, v___x_3004_);
    return v___x_3005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4____boxed(
    mut v_a_3006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3007_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
    return v_res_3007_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(
    mut v_lctx_3008_: *mut crate::leanh::LeanObject,
    mut v_binderName_3009_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3010_: u8,
    mut v_a_3011_: *mut crate::leanh::LeanObject,
    mut v_a_3012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_hygienic_3010_ == 0 {
        let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3014_ = l_Lean_LocalContext_getUnusedName(v_lctx_3008_, v_binderName_3009_);
        v___x_3015_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3015_, 0, v___x_3014_);
        return v___x_3015_;
    } else {
        let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3016_ = l_Lean_Core_mkFreshUserName(v_binderName_3009_, v_a_3011_, v_a_3012_);
        return v___x_3016_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg___boxed(
    mut v_lctx_3017_: *mut crate::leanh::LeanObject,
    mut v_binderName_3018_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hygienic_boxed_3023_: u8 = 0;
    let mut v_res_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hygienic_boxed_3023_ = (crate::leanh::lean_unbox(v_hygienic_3019_) as u8);
    v_res_3024_ =
        l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore___redArg(
            v_lctx_3017_,
            v_binderName_3018_,
            v_hygienic_boxed_3023_,
            v_a_3020_,
            v_a_3021_,
        );
    crate::leanh::lean_dec(v_a_3021_);
    crate::leanh::lean_dec_ref(v_a_3020_);
    crate::leanh::lean_dec_ref(v_lctx_3017_);
    return v_res_3024_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(
    mut v_lctx_3025_: *mut crate::leanh::LeanObject,
    mut v_binderName_3026_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3027_: u8,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_lctx_3034_: *mut crate::leanh::LeanObject,
    mut v_binderName_3035_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
    mut v_a_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hygienic_boxed_3042_: u8 = 0;
    let mut v_res_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hygienic_boxed_3042_ = (crate::leanh::lean_unbox(v_hygienic_3036_) as u8);
    v_res_3043_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkFreshBinderNameForTacticCore(
        v_lctx_3034_,
        v_binderName_3035_,
        v_hygienic_boxed_3042_,
        v_a_3037_,
        v_a_3038_,
        v_a_3039_,
        v_a_3040_,
    );
    crate::leanh::lean_dec(v_a_3040_);
    crate::leanh::lean_dec_ref(v_a_3039_);
    crate::leanh::lean_dec(v_a_3038_);
    crate::leanh::lean_dec_ref(v_a_3037_);
    crate::leanh::lean_dec_ref(v_lctx_3034_);
    return v_res_3043_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
    mut v_opts_3044_: *mut crate::leanh::LeanObject,
    mut v_opt_3045_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3046_ = crate::leanh::lean_ctor_get(v_opt_3045_, 0);
    v_defValue_3047_ = crate::leanh::lean_ctor_get(v_opt_3045_, 1);
    v_map_3048_ = crate::leanh::lean_ctor_get(v_opts_3044_, 0);
    v___x_3049_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3048_,
            v_name_3046_,
        );
    if crate::leanh::lean_obj_tag(v___x_3049_) == 0 {
        let mut v___x_3050_: u8 = 0;
        v___x_3050_ = (crate::leanh::lean_unbox(v_defValue_3047_) as u8);
        return v___x_3050_;
    } else {
        let mut v_val_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3051_ = crate::leanh::lean_ctor_get(v___x_3049_, 0);
        crate::leanh::lean_inc(v_val_3051_);
        crate::leanh::lean_dec_ref_known(v___x_3049_, 1);
        if crate::leanh::lean_obj_tag(v_val_3051_) == 1 {
            let mut v_v_3052_: u8 = 0;
            v_v_3052_ = crate::leanh::lean_ctor_get_uint8(v_val_3051_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3051_, 0);
            return v_v_3052_;
        } else {
            let mut v___x_3053_: u8 = 0;
            crate::leanh::lean_dec(v_val_3051_);
            v___x_3053_ = (crate::leanh::lean_unbox(v_defValue_3047_) as u8);
            return v___x_3053_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0___boxed(
    mut v_opts_3054_: *mut crate::leanh::LeanObject,
    mut v_opt_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
        v_opts_3054_,
        v_opt_3055_,
    );
    crate::leanh::lean_dec_ref(v_opt_3055_);
    crate::leanh::lean_dec_ref(v_opts_3054_);
    v_r_3057_ = crate::leanh::lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic___redArg(
    mut v_binderName_3058_: *mut crate::leanh::LeanObject,
    mut v_a_3059_: *mut crate::leanh::LeanObject,
    mut v_a_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_3063_ = crate::leanh::lean_ctor_get(v_a_3059_, 2);
    v_options_3064_ = crate::leanh::lean_ctor_get(v_a_3060_, 2);
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
    mut v_binderName_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_a_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(
        v_binderName_3068_,
        v_a_3069_,
        v_a_3070_,
        v_a_3071_,
    );
    crate::leanh::lean_dec(v_a_3071_);
    crate::leanh::lean_dec_ref(v_a_3070_);
    crate::leanh::lean_dec_ref(v_a_3069_);
    return v_res_3073_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic(
    mut v_binderName_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(
        v_binderName_3074_,
        v_a_3075_,
        v_a_3077_,
        v_a_3078_,
    );
    return v___x_3080_;
}
pub unsafe fn l_Lean_Meta_mkFreshBinderNameForTactic___boxed(
    mut v_binderName_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ = l_Lean_Meta_mkFreshBinderNameForTactic(
        v_binderName_3081_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
    );
    crate::leanh::lean_dec(v_a_3085_);
    crate::leanh::lean_dec_ref(v_a_3084_);
    crate::leanh::lean_dec(v_a_3083_);
    crate::leanh::lean_dec_ref(v_a_3082_);
    return v_res_3087_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(
    mut v_preserveBinderNames_3091_: u8,
    mut v_hygienic_3092_: u8,
    mut v_lctx_3093_: *mut crate::leanh::LeanObject,
    mut v_binderName_3094_: *mut crate::leanh::LeanObject,
    mut v_rest_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_a_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v_binderName_3094_);
                    v___x_3124_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg___closed__1;
                    v___x_3125_ = l_Lean_Core_mkFreshUserName(v___x_3124_, v_a_3096_, v_a_3097_);
                    if crate::leanh::lean_obj_tag(v___x_3125_) == 0 {
                        v_a_3126_ = crate::leanh::lean_ctor_get(v___x_3125_, 0);
                        crate::leanh::lean_inc(v_a_3126_);
                        crate::leanh::lean_dec_ref_known(v___x_3125_, 1);
                        v_binderName_3100_ = v_a_3126_;
                        v___y_3101_ = v_a_3096_;
                        v___y_3102_ = v_a_3097_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_rest_3095_);
                        v_a_3127_ = crate::leanh::lean_ctor_get(v___x_3125_, 0);
                        v_isSharedCheck_3134_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3125_)) as u8;
                        if v_isSharedCheck_3134_ == 0 {
                            v___x_3129_ = v___x_3125_;
                            v_isShared_3130_ = v_isSharedCheck_3134_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3127_);
                            crate::leanh::lean_dec(v___x_3125_);
                            v___x_3129_ = crate::leanh::lean_box(0);
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
                    if crate::leanh::lean_obj_tag(v___x_3103_) == 0 {
                        v_a_3104_ = crate::leanh::lean_ctor_get(v___x_3103_, 0);
                        v_isSharedCheck_3112_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3103_)) as u8;
                        if v_isSharedCheck_3112_ == 0 {
                            v___x_3106_ = v___x_3103_;
                            v_isShared_3107_ = v_isSharedCheck_3112_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3104_);
                            crate::leanh::lean_dec(v___x_3103_);
                            v___x_3106_ = crate::leanh::lean_box(0);
                            v_isShared_3107_ = v_isSharedCheck_3112_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_rest_3095_);
                        v_a_3113_ = crate::leanh::lean_ctor_get(v___x_3103_, 0);
                        v_isSharedCheck_3120_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3103_)) as u8;
                        if v_isSharedCheck_3120_ == 0 {
                            v___x_3115_ = v___x_3103_;
                            v_isShared_3116_ = v_isSharedCheck_3120_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3113_);
                            crate::leanh::lean_dec(v___x_3103_);
                            v___x_3115_ = crate::leanh::lean_box(0);
                            v_isShared_3116_ = v_isSharedCheck_3120_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_3121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3121_, 0, v_binderName_3100_);
                    crate::leanh::lean_ctor_set(v___x_3121_, 1, v_rest_3095_);
                    v___x_3122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3122_, 0, v___x_3121_);
                    return v___x_3122_;
                }
            }
            2 => {
                v___x_3108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3108_, 0, v_a_3104_);
                crate::leanh::lean_ctor_set(v___x_3108_, 1, v_rest_3095_);
                if v_isShared_3107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3106_, 0, v___x_3108_);
                    v___x_3110_ = v___x_3106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
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
                    v_reuseFailAlloc_3119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
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
                    v_reuseFailAlloc_3133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
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
    mut v_preserveBinderNames_3135_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3136_: *mut crate::leanh::LeanObject,
    mut v_lctx_3137_: *mut crate::leanh::LeanObject,
    mut v_binderName_3138_: *mut crate::leanh::LeanObject,
    mut v_rest_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3143_: u8 = 0;
    let mut v_hygienic_boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3143_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_3135_) as u8);
    v_hygienic_boxed_3144_ = (crate::leanh::lean_unbox(v_hygienic_3136_) as u8);
    v_res_3145_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_boxed_3143_, v_hygienic_boxed_3144_, v_lctx_3137_, v_binderName_3138_, v_rest_3139_, v_a_3140_, v_a_3141_);
    crate::leanh::lean_dec(v_a_3141_);
    crate::leanh::lean_dec_ref(v_a_3140_);
    crate::leanh::lean_dec_ref(v_lctx_3137_);
    return v_res_3145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName(
    mut v_preserveBinderNames_3146_: u8,
    mut v_hygienic_3147_: u8,
    mut v_lctx_3148_: *mut crate::leanh::LeanObject,
    mut v_binderName_3149_: *mut crate::leanh::LeanObject,
    mut v_rest_3150_: *mut crate::leanh::LeanObject,
    mut v_a_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3156_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3146_, v_hygienic_3147_, v_lctx_3148_, v_binderName_3149_, v_rest_3150_, v_a_3153_, v_a_3154_);
    return v___x_3156_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___boxed(
    mut v_preserveBinderNames_3157_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3158_: *mut crate::leanh::LeanObject,
    mut v_lctx_3159_: *mut crate::leanh::LeanObject,
    mut v_binderName_3160_: *mut crate::leanh::LeanObject,
    mut v_rest_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3167_: u8 = 0;
    let mut v_hygienic_boxed_3168_: u8 = 0;
    let mut v_res_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3167_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_3157_) as u8);
    v_hygienic_boxed_3168_ = (crate::leanh::lean_unbox(v_hygienic_3158_) as u8);
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
    crate::leanh::lean_dec(v_a_3165_);
    crate::leanh::lean_dec_ref(v_a_3164_);
    crate::leanh::lean_dec(v_a_3163_);
    crate::leanh::lean_dec_ref(v_a_3162_);
    crate::leanh::lean_dec_ref(v_lctx_3159_);
    return v_res_3169_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(
    mut v_preserveBinderNames_3174_: u8,
    mut v_hygienic_3175_: u8,
    mut v_useNamesForExplicitOnly_3176_: u8,
    mut v_lctx_3177_: *mut crate::leanh::LeanObject,
    mut v_binderName_3178_: *mut crate::leanh::LeanObject,
    mut v_isExplicit_3179_: u8,
    mut v_x_3180_: *mut crate::leanh::LeanObject,
    mut v_a_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3180_) == 0 {
                    v___x_3184_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3174_, v_hygienic_3175_, v_lctx_3177_, v_binderName_3178_, v_x_3180_, v_a_3181_, v_a_3182_);
                    return v___x_3184_;
                } else {
                    v_head_3185_ = crate::leanh::lean_ctor_get(v_x_3180_, 0);
                    v_tail_3186_ = crate::leanh::lean_ctor_get(v_x_3180_, 1);
                    if v_useNamesForExplicitOnly_3176_ == 0 {
                        crate::leanh::lean_inc(v_tail_3186_);
                        crate::leanh::lean_inc(v_head_3185_);
                        crate::leanh::lean_dec_ref_known(v_x_3180_, 2);
                        state = 1;
                        continue;
                    } else {
                        if v_isExplicit_3179_ == 0 {
                            v___x_3193_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3174_, v_hygienic_3175_, v_lctx_3177_, v_binderName_3178_, v_x_3180_, v_a_3181_, v_a_3182_);
                            return v___x_3193_;
                        } else {
                            crate::leanh::lean_inc(v_tail_3186_);
                            crate::leanh::lean_inc(v_head_3185_);
                            crate::leanh::lean_dec_ref_known(v_x_3180_, 2);
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
                    crate::leanh::lean_dec(v_binderName_3178_);
                    v___x_3190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3190_, 0, v_head_3185_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 1, v_tail_3186_);
                    v___x_3191_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3191_, 0, v___x_3190_);
                    return v___x_3191_;
                } else {
                    crate::leanh::lean_dec(v_head_3185_);
                    v___x_3192_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp_mkAuxNameWithoutGivenName___redArg(v_preserveBinderNames_3174_, v_hygienic_3175_, v_lctx_3177_, v_binderName_3178_, v_tail_3186_, v_a_3181_, v_a_3182_);
                    return v___x_3192_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg___boxed(
    mut v_preserveBinderNames_3194_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3195_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3196_: *mut crate::leanh::LeanObject,
    mut v_lctx_3197_: *mut crate::leanh::LeanObject,
    mut v_binderName_3198_: *mut crate::leanh::LeanObject,
    mut v_isExplicit_3199_: *mut crate::leanh::LeanObject,
    mut v_x_3200_: *mut crate::leanh::LeanObject,
    mut v_a_3201_: *mut crate::leanh::LeanObject,
    mut v_a_3202_: *mut crate::leanh::LeanObject,
    mut v_a_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3204_: u8 = 0;
    let mut v_hygienic_boxed_3205_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3206_: u8 = 0;
    let mut v_isExplicit_boxed_3207_: u8 = 0;
    let mut v_res_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3204_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_3194_) as u8);
    v_hygienic_boxed_3205_ = (crate::leanh::lean_unbox(v_hygienic_3195_) as u8);
    v_useNamesForExplicitOnly_boxed_3206_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_3196_) as u8);
    v_isExplicit_boxed_3207_ = (crate::leanh::lean_unbox(v_isExplicit_3199_) as u8);
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
    crate::leanh::lean_dec(v_a_3202_);
    crate::leanh::lean_dec_ref(v_a_3201_);
    crate::leanh::lean_dec_ref(v_lctx_3197_);
    return v_res_3208_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp(
    mut v_preserveBinderNames_3209_: u8,
    mut v_hygienic_3210_: u8,
    mut v_useNamesForExplicitOnly_3211_: u8,
    mut v_lctx_3212_: *mut crate::leanh::LeanObject,
    mut v_binderName_3213_: *mut crate::leanh::LeanObject,
    mut v_isExplicit_3214_: u8,
    mut v_x_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_preserveBinderNames_3222_: *mut crate::leanh::LeanObject,
    mut v_hygienic_3223_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3224_: *mut crate::leanh::LeanObject,
    mut v_lctx_3225_: *mut crate::leanh::LeanObject,
    mut v_binderName_3226_: *mut crate::leanh::LeanObject,
    mut v_isExplicit_3227_: *mut crate::leanh::LeanObject,
    mut v_x_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3234_: u8 = 0;
    let mut v_hygienic_boxed_3235_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3236_: u8 = 0;
    let mut v_isExplicit_boxed_3237_: u8 = 0;
    let mut v_res_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3234_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_3222_) as u8);
    v_hygienic_boxed_3235_ = (crate::leanh::lean_unbox(v_hygienic_3223_) as u8);
    v_useNamesForExplicitOnly_boxed_3236_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_3224_) as u8);
    v_isExplicit_boxed_3237_ = (crate::leanh::lean_unbox(v_isExplicit_3227_) as u8);
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
    crate::leanh::lean_dec(v_a_3232_);
    crate::leanh::lean_dec_ref(v_a_3231_);
    crate::leanh::lean_dec(v_a_3230_);
    crate::leanh::lean_dec_ref(v_a_3229_);
    crate::leanh::lean_dec_ref(v_lctx_3225_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
    mut v_mvarId_3239_: *mut crate::leanh::LeanObject,
    mut v_x_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3250_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_a_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3239_,
                    v_x_3240_,
                    v___y_3241_,
                    v___y_3242_,
                    v___y_3243_,
                    v___y_3244_,
                );
                if crate::leanh::lean_obj_tag(v___x_3246_) == 0 {
                    v_a_3247_ = crate::leanh::lean_ctor_get(v___x_3246_, 0);
                    v_isSharedCheck_3254_ = (!crate::leanh::lean_is_exclusive(v___x_3246_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v___x_3249_ = v___x_3246_;
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3247_);
                        crate::leanh::lean_dec(v___x_3246_);
                        v___x_3249_ = crate::leanh::lean_box(0);
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3255_ = crate::leanh::lean_ctor_get(v___x_3246_, 0);
                    v_isSharedCheck_3262_ = (!crate::leanh::lean_is_exclusive(v___x_3246_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3257_ = v___x_3246_;
                        v_isShared_3258_ = v_isSharedCheck_3262_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3255_);
                        crate::leanh::lean_dec(v___x_3246_);
                        v___x_3257_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
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
                    v_reuseFailAlloc_3261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
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
    mut v_mvarId_3263_: *mut crate::leanh::LeanObject,
    mut v_x_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2___redArg(
        v_mvarId_3263_,
        v_x_3264_,
        v___y_3265_,
        v___y_3266_,
        v___y_3267_,
        v___y_3268_,
    );
    crate::leanh::lean_dec(v___y_3268_);
    crate::leanh::lean_dec_ref(v___y_3267_);
    crate::leanh::lean_dec(v___y_3266_);
    crate::leanh::lean_dec_ref(v___y_3265_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(
    mut v_00_u03b1_3271_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3272_: *mut crate::leanh::LeanObject,
    mut v_x_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
    mut v___y_3277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3280_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3281_: *mut crate::leanh::LeanObject,
    mut v_x_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3288_ = l_Lean_MVarId_withContext___at___00Lean_Meta_introNCore_spec__2(
        v_00_u03b1_3280_,
        v_mvarId_3281_,
        v_x_3282_,
        v___y_3283_,
        v___y_3284_,
        v___y_3285_,
        v___y_3286_,
    );
    crate::leanh::lean_dec(v___y_3286_);
    crate::leanh::lean_dec_ref(v___y_3285_);
    crate::leanh::lean_dec(v___y_3284_);
    crate::leanh::lean_dec_ref(v___y_3283_);
    return v_res_3288_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(
    mut v_sz_3289_: usize,
    mut v_i_3290_: usize,
    mut v_bs_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3292_: u8 = 0;
    let mut v_v_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: usize = 0;
    let mut v___x_3298_: usize = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3292_ = lean_usize_dec_lt(v_i_3290_, v_sz_3289_);
                if v___x_3292_ == 0 {
                    return v_bs_3291_;
                } else {
                    v_v_3293_ = lean_array_uget(v_bs_3291_, v_i_3290_);
                    v___x_3294_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3295_ = lean_array_uset(v_bs_3291_, v_i_3290_, v___x_3294_);
                    v___x_3296_ = l_Lean_Expr_fvarId_x21(v_v_3293_);
                    crate::leanh::lean_dec(v_v_3293_);
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
    mut v_sz_3301_: *mut crate::leanh::LeanObject,
    mut v_i_3302_: *mut crate::leanh::LeanObject,
    mut v_bs_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3304_: usize = 0;
    let mut v_i_boxed_3305_: usize = 0;
    let mut v_res_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3304_ = crate::leanh::lean_unbox_usize(v_sz_3301_);
    crate::leanh::lean_dec(v_sz_3301_);
    v_i_boxed_3305_ = crate::leanh::lean_unbox_usize(v_i_3302_);
    crate::leanh::lean_dec(v_i_3302_);
    v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_introNCore_spec__1(v_sz_boxed_3304_, v_i_boxed_3305_, v_bs_3303_);
    return v_res_3306_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(
    mut v_e_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut v_unused_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3310_ = l_Lean_Expr_hasMVar(v_e_3307_);
                if v___x_3310_ == 0 {
                    v___x_3311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3311_, 0, v_e_3307_);
                    return v___x_3311_;
                } else {
                    v___x_3312_ = lean_st_ref_get(v___y_3308_);
                    v_mctx_3313_ = crate::leanh::lean_ctor_get(v___x_3312_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3313_);
                    crate::leanh::lean_dec(v___x_3312_);
                    v___x_3314_ = l_Lean_instantiateMVarsCore(v_mctx_3313_, v_e_3307_);
                    v_fst_3315_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
                    crate::leanh::lean_inc(v_fst_3315_);
                    v_snd_3316_ = crate::leanh::lean_ctor_get(v___x_3314_, 1);
                    crate::leanh::lean_inc(v_snd_3316_);
                    crate::leanh::lean_dec_ref(v___x_3314_);
                    v___x_3317_ = lean_st_ref_take(v___y_3308_);
                    v_cache_3318_ = crate::leanh::lean_ctor_get(v___x_3317_, 1);
                    v_zetaDeltaFVarIds_3319_ = crate::leanh::lean_ctor_get(v___x_3317_, 2);
                    v_postponed_3320_ = crate::leanh::lean_ctor_get(v___x_3317_, 3);
                    v_diag_3321_ = crate::leanh::lean_ctor_get(v___x_3317_, 4);
                    v_isSharedCheck_3330_ = (!crate::leanh::lean_is_exclusive(v___x_3317_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v_unused_3331_ = crate::leanh::lean_ctor_get(v___x_3317_, 0);
                        crate::leanh::lean_dec(v_unused_3331_);
                        v___x_3323_ = v___x_3317_;
                        v_isShared_3324_ = v_isSharedCheck_3330_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3321_);
                        crate::leanh::lean_inc(v_postponed_3320_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3319_);
                        crate::leanh::lean_inc(v_cache_3318_);
                        crate::leanh::lean_dec(v___x_3317_);
                        v___x_3323_ = crate::leanh::lean_box(0);
                        v_isShared_3324_ = v_isSharedCheck_3330_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3323_, 0, v_snd_3316_);
                    v___x_3326_ = v___x_3323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_snd_3316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_cache_3318_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3329_,
                        2,
                        v_zetaDeltaFVarIds_3319_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_postponed_3320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 4, v_diag_3321_);
                    v___x_3326_ = v_reuseFailAlloc_3329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3327_ = lean_st_ref_set(v___y_3308_, v___x_3326_);
                v___x_3328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3328_, 0, v_fst_3315_);
                return v___x_3328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg___boxed(
    mut v_e_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_3332_, v___y_3333_);
    crate::leanh::lean_dec(v___y_3333_);
    return v_res_3335_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v_r_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_unused_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3338_ = lean_st_ref_get(v___y_3336_);
                v_ngen_3339_ = crate::leanh::lean_ctor_get(v___x_3338_, 2);
                crate::leanh::lean_inc_ref(v_ngen_3339_);
                crate::leanh::lean_dec(v___x_3338_);
                v_namePrefix_3340_ = crate::leanh::lean_ctor_get(v_ngen_3339_, 0);
                v_idx_3341_ = crate::leanh::lean_ctor_get(v_ngen_3339_, 1);
                v_isSharedCheck_3370_ = (!crate::leanh::lean_is_exclusive(v_ngen_3339_)) as u8;
                if v_isSharedCheck_3370_ == 0 {
                    v___x_3343_ = v_ngen_3339_;
                    v_isShared_3344_ = v_isSharedCheck_3370_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_3341_);
                    crate::leanh::lean_inc(v_namePrefix_3340_);
                    crate::leanh::lean_dec(v_ngen_3339_);
                    v___x_3343_ = crate::leanh::lean_box(0);
                    v_isShared_3344_ = v_isSharedCheck_3370_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3345_ = lean_st_ref_take(v___y_3336_);
                v_env_3346_ = crate::leanh::lean_ctor_get(v___x_3345_, 0);
                v_nextMacroScope_3347_ = crate::leanh::lean_ctor_get(v___x_3345_, 1);
                v_auxDeclNGen_3348_ = crate::leanh::lean_ctor_get(v___x_3345_, 3);
                v_traceState_3349_ = crate::leanh::lean_ctor_get(v___x_3345_, 4);
                v_cache_3350_ = crate::leanh::lean_ctor_get(v___x_3345_, 5);
                v_messages_3351_ = crate::leanh::lean_ctor_get(v___x_3345_, 6);
                v_infoState_3352_ = crate::leanh::lean_ctor_get(v___x_3345_, 7);
                v_snapshotTasks_3353_ = crate::leanh::lean_ctor_get(v___x_3345_, 8);
                v_isSharedCheck_3368_ = (!crate::leanh::lean_is_exclusive(v___x_3345_)) as u8;
                if v_isSharedCheck_3368_ == 0 {
                    v_unused_3369_ = crate::leanh::lean_ctor_get(v___x_3345_, 2);
                    crate::leanh::lean_dec(v_unused_3369_);
                    v___x_3355_ = v___x_3345_;
                    v_isShared_3356_ = v_isSharedCheck_3368_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3353_);
                    crate::leanh::lean_inc(v_infoState_3352_);
                    crate::leanh::lean_inc(v_messages_3351_);
                    crate::leanh::lean_inc(v_cache_3350_);
                    crate::leanh::lean_inc(v_traceState_3349_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3348_);
                    crate::leanh::lean_inc(v_nextMacroScope_3347_);
                    crate::leanh::lean_inc(v_env_3346_);
                    crate::leanh::lean_dec(v___x_3345_);
                    v___x_3355_ = crate::leanh::lean_box(0);
                    v_isShared_3356_ = v_isSharedCheck_3368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_3341_);
                crate::leanh::lean_inc(v_namePrefix_3340_);
                v_r_3357_ = l_Lean_Name_num___override(v_namePrefix_3340_, v_idx_3341_);
                v___x_3358_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3359_ = lean_nat_add(v_idx_3341_, v___x_3358_);
                crate::leanh::lean_dec(v_idx_3341_);
                if v_isShared_3344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3343_, 1, v___x_3359_);
                    v___x_3361_ = v___x_3343_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_namePrefix_3340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 1, v___x_3359_);
                    v___x_3361_ = v_reuseFailAlloc_3367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3355_, 2, v___x_3361_);
                    v___x_3363_ = v___x_3355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3366_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_env_3346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_nextMacroScope_3347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 2, v___x_3361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 3, v_auxDeclNGen_3348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 4, v_traceState_3349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 5, v_cache_3350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 6, v_messages_3351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 7, v_infoState_3352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3366_, 8, v_snapshotTasks_3353_);
                    v___x_3363_ = v_reuseFailAlloc_3366_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3364_ = lean_st_ref_set(v___y_3336_, v___x_3363_);
                v___x_3365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3365_, 0, v_r_3357_);
                return v___x_3365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg___boxed(
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_3371_);
    crate::leanh::lean_dec(v___y_3371_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3379_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_3377_);
                v_a_3380_ = crate::leanh::lean_ctor_get(v___x_3379_, 0);
                v_isSharedCheck_3387_ = (!crate::leanh::lean_is_exclusive(v___x_3379_)) as u8;
                if v_isSharedCheck_3387_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    v_isShared_3383_ = v_isSharedCheck_3387_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3380_);
                    crate::leanh::lean_dec(v___x_3379_);
                    v___x_3382_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
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
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    crate::leanh::lean_dec(v___y_3391_);
    crate::leanh::lean_dec_ref(v___y_3390_);
    crate::leanh::lean_dec(v___y_3389_);
    crate::leanh::lean_dec_ref(v___y_3388_);
    return v_res_3393_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(
    mut v_fvars_3394_: *mut crate::leanh::LeanObject,
    mut v_j_3395_: *mut crate::leanh::LeanObject,
    mut v_x_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3406_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut v_a_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp(
                    crate::leanh::lean_box(0),
                    v_fvars_3394_,
                    v_j_3395_,
                    v_x_3396_,
                    v___y_3397_,
                    v___y_3398_,
                    v___y_3399_,
                    v___y_3400_,
                );
                if crate::leanh::lean_obj_tag(v___x_3402_) == 0 {
                    v_a_3403_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    v_isSharedCheck_3410_ = (!crate::leanh::lean_is_exclusive(v___x_3402_)) as u8;
                    if v_isSharedCheck_3410_ == 0 {
                        v___x_3405_ = v___x_3402_;
                        v_isShared_3406_ = v_isSharedCheck_3410_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3403_);
                        crate::leanh::lean_dec(v___x_3402_);
                        v___x_3405_ = crate::leanh::lean_box(0);
                        v_isShared_3406_ = v_isSharedCheck_3410_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3411_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    v_isSharedCheck_3418_ = (!crate::leanh::lean_is_exclusive(v___x_3402_)) as u8;
                    if v_isSharedCheck_3418_ == 0 {
                        v___x_3413_ = v___x_3402_;
                        v_isShared_3414_ = v_isSharedCheck_3418_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3411_);
                        crate::leanh::lean_dec(v___x_3402_);
                        v___x_3413_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
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
                    v_reuseFailAlloc_3417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
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
    mut v_fvars_3419_: *mut crate::leanh::LeanObject,
    mut v_j_3420_: *mut crate::leanh::LeanObject,
    mut v_x_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
    mut v___y_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_3419_, v_j_3420_, v_x_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
    crate::leanh::lean_dec(v___y_3425_);
    crate::leanh::lean_dec_ref(v___y_3424_);
    crate::leanh::lean_dec(v___y_3423_);
    crate::leanh::lean_dec_ref(v___y_3422_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(
    mut v_fvars_3428_: *mut crate::leanh::LeanObject,
    mut v_j_3429_: *mut crate::leanh::LeanObject,
    mut v_x_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
    mut v___y_3432_: *mut crate::leanh::LeanObject,
    mut v___y_3433_: *mut crate::leanh::LeanObject,
    mut v___y_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3436_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_3428_, v_j_3429_, v_x_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
                if crate::leanh::lean_obj_tag(v___x_3436_) == 0 {
                    v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3444_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3444_ == 0 {
                        v___x_3439_ = v___x_3436_;
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3437_);
                        crate::leanh::lean_dec(v___x_3436_);
                        v___x_3439_ = crate::leanh::lean_box(0);
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3452_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3452_ == 0 {
                        v___x_3447_ = v___x_3436_;
                        v_isShared_3448_ = v_isSharedCheck_3452_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3445_);
                        crate::leanh::lean_dec(v___x_3436_);
                        v___x_3447_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
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
                    v_reuseFailAlloc_3451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
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
    mut v_fvars_3453_: *mut crate::leanh::LeanObject,
    mut v_j_3454_: *mut crate::leanh::LeanObject,
    mut v_x_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_3453_, v_j_3454_, v_x_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
    crate::leanh::lean_dec(v___y_3459_);
    crate::leanh::lean_dec_ref(v___y_3458_);
    crate::leanh::lean_dec(v___y_3457_);
    crate::leanh::lean_dec_ref(v___y_3456_);
    return v_res_3461_;
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(
    mut v_00_u03b1_3462_: *mut crate::leanh::LeanObject,
    mut v_fvars_3463_: *mut crate::leanh::LeanObject,
    mut v_j_3464_: *mut crate::leanh::LeanObject,
    mut v_x_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3471_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___redArg(v_fvars_3463_, v_j_3464_, v_x_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
    return v___x_3471_;
}
pub unsafe fn l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed(
    mut v_00_u03b1_3472_: *mut crate::leanh::LeanObject,
    mut v_fvars_3473_: *mut crate::leanh::LeanObject,
    mut v_j_3474_: *mut crate::leanh::LeanObject,
    mut v_x_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1(v_00_u03b1_3472_, v_fvars_3473_, v_j_3474_, v_x_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
    crate::leanh::lean_dec(v___y_3479_);
    crate::leanh::lean_dec_ref(v___y_3478_);
    crate::leanh::lean_dec(v___y_3477_);
    crate::leanh::lean_dec_ref(v___y_3476_);
    return v_res_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(
    mut v_x_3482_: *mut crate::leanh::LeanObject,
    mut v_x_3483_: *mut crate::leanh::LeanObject,
    mut v_x_3484_: *mut crate::leanh::LeanObject,
    mut v_x_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3486_ = crate::leanh::lean_ctor_get(v_x_3482_, 0);
                v_vs_3487_ = crate::leanh::lean_ctor_get(v_x_3482_, 1);
                v_isSharedCheck_3511_ = (!crate::leanh::lean_is_exclusive(v_x_3482_)) as u8;
                if v_isSharedCheck_3511_ == 0 {
                    v___x_3489_ = v_x_3482_;
                    v_isShared_3490_ = v_isSharedCheck_3511_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3487_);
                    crate::leanh::lean_inc(v_ks_3486_);
                    crate::leanh::lean_dec(v_x_3482_);
                    v___x_3489_ = crate::leanh::lean_box(0);
                    v_isShared_3490_ = v_isSharedCheck_3511_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3491_ = lean_array_get_size(v_ks_3486_);
                v___x_3492_ = lean_nat_dec_lt(v_x_3483_, v___x_3491_);
                if v___x_3492_ == 0 {
                    crate::leanh::lean_dec(v_x_3483_);
                    v___x_3493_ = lean_array_push(v_ks_3486_, v_x_3484_);
                    v___x_3494_ = lean_array_push(v_vs_3487_, v_x_3485_);
                    if v_isShared_3490_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3489_, 1, v___x_3494_);
                        crate::leanh::lean_ctor_set(v___x_3489_, 0, v___x_3493_);
                        v___x_3496_ = v___x_3489_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3497_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3493_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3494_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_ks_3486_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_vs_3487_);
                            v___x_3501_ = v_reuseFailAlloc_3505_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3506_ = lean_array_fset(v_ks_3486_, v_x_3483_, v_x_3484_);
                        v___x_3507_ = lean_array_fset(v_vs_3487_, v_x_3483_, v_x_3485_);
                        crate::leanh::lean_dec(v_x_3483_);
                        if v_isShared_3490_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3489_, 1, v___x_3507_);
                            crate::leanh::lean_ctor_set(v___x_3489_, 0, v___x_3506_);
                            v___x_3509_ = v___x_3489_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3510_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3506_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3510_, 1, v___x_3507_);
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
                v___x_3502_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3503_ = lean_nat_add(v_x_3483_, v___x_3502_);
                crate::leanh::lean_dec(v_x_3483_);
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
    mut v_n_3512_: *mut crate::leanh::LeanObject,
    mut v_k_3513_: *mut crate::leanh::LeanObject,
    mut v_v_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3515_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_3521_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__0);
    v___x_3522_ = lean_usize_sub(v___x_3521_, v___x_3520_);
    return v___x_3522_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3523_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_x_3524_: *mut crate::leanh::LeanObject,
    mut v_x_3525_: usize,
    mut v_x_3526_: usize,
    mut v_x_3527_: *mut crate::leanh::LeanObject,
    mut v_x_3528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: usize = 0;
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: usize = 0;
    let mut v_j_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v_v_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_node_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3565_: usize = 0;
    let mut v___x_3566_: usize = 0;
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3573_: u8 = 0;
    let mut v_unused_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: u8 = 0;
    let mut v_ks_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: usize = 0;
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v_reuseFailAlloc_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3524_) == 0 {
                    v_es_3529_ = crate::leanh::lean_ctor_get(v_x_3524_, 0);
                    v___x_3530_ = 5usize;
                    v___x_3531_ = 1usize;
                    v___x_3532_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__1);
                    v___x_3533_ = lean_usize_land(v_x_3525_, v___x_3532_);
                    v_j_3534_ = lean_usize_to_nat(v___x_3533_);
                    v___x_3535_ = lean_array_get_size(v_es_3529_);
                    v___x_3536_ = lean_nat_dec_lt(v_j_3534_, v___x_3535_);
                    if v___x_3536_ == 0 {
                        crate::leanh::lean_dec(v_j_3534_);
                        crate::leanh::lean_dec(v_x_3528_);
                        crate::leanh::lean_dec(v_x_3527_);
                        return v_x_3524_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3529_);
                        v_isSharedCheck_3573_ = (!crate::leanh::lean_is_exclusive(v_x_3524_)) as u8;
                        if v_isSharedCheck_3573_ == 0 {
                            v_unused_3574_ = crate::leanh::lean_ctor_get(v_x_3524_, 0);
                            crate::leanh::lean_dec(v_unused_3574_);
                            v___x_3538_ = v_x_3524_;
                            v_isShared_3539_ = v_isSharedCheck_3573_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3524_);
                            v___x_3538_ = crate::leanh::lean_box(0);
                            v_isShared_3539_ = v_isSharedCheck_3573_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3575_ = crate::leanh::lean_ctor_get(v_x_3524_, 0);
                    v_vs_3576_ = crate::leanh::lean_ctor_get(v_x_3524_, 1);
                    v_isSharedCheck_3596_ = (!crate::leanh::lean_is_exclusive(v_x_3524_)) as u8;
                    if v_isSharedCheck_3596_ == 0 {
                        v___x_3578_ = v_x_3524_;
                        v_isShared_3579_ = v_isSharedCheck_3596_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3576_);
                        crate::leanh::lean_inc(v_ks_3575_);
                        crate::leanh::lean_dec(v_x_3524_);
                        v___x_3578_ = crate::leanh::lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3596_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3540_ = lean_array_fget(v_es_3529_, v_j_3534_);
                v___x_3541_ = crate::leanh::lean_box(0);
                v_xs_x27_3542_ = lean_array_fset(v_es_3529_, v_j_3534_, v___x_3541_);
                match crate::leanh::lean_obj_tag(v_v_3540_) {
                    0 => {
                        v_key_3549_ = crate::leanh::lean_ctor_get(v_v_3540_, 0);
                        v_val_3550_ = crate::leanh::lean_ctor_get(v_v_3540_, 1);
                        v_isSharedCheck_3560_ = (!crate::leanh::lean_is_exclusive(v_v_3540_)) as u8;
                        if v_isSharedCheck_3560_ == 0 {
                            v___x_3552_ = v_v_3540_;
                            v_isShared_3553_ = v_isSharedCheck_3560_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3550_);
                            crate::leanh::lean_inc(v_key_3549_);
                            crate::leanh::lean_dec(v_v_3540_);
                            v___x_3552_ = crate::leanh::lean_box(0);
                            v_isShared_3553_ = v_isSharedCheck_3560_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3561_ = crate::leanh::lean_ctor_get(v_v_3540_, 0);
                        v_isSharedCheck_3571_ = (!crate::leanh::lean_is_exclusive(v_v_3540_)) as u8;
                        if v_isSharedCheck_3571_ == 0 {
                            v___x_3563_ = v_v_3540_;
                            v_isShared_3564_ = v_isSharedCheck_3571_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3561_);
                            crate::leanh::lean_dec(v_v_3540_);
                            v___x_3563_ = crate::leanh::lean_box(0);
                            v_isShared_3564_ = v_isSharedCheck_3571_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3572_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3572_, 0, v_x_3527_);
                        crate::leanh::lean_ctor_set(v___x_3572_, 1, v_x_3528_);
                        v___y_3544_ = v___x_3572_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3545_ = lean_array_fset(v_xs_x27_3542_, v_j_3534_, v___y_3544_);
                crate::leanh::lean_dec(v_j_3534_);
                if v_isShared_3539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3538_, 0, v___x_3545_);
                    v___x_3547_ = v___x_3538_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
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
                    crate::leanh::lean_del_object(v___x_3552_);
                    v___x_3555_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3549_,
                        v_val_3550_,
                        v_x_3527_,
                        v_x_3528_,
                    );
                    v___x_3556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3556_, 0, v___x_3555_);
                    v___y_3544_ = v___x_3556_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3550_);
                    crate::leanh::lean_dec(v_key_3549_);
                    if v_isShared_3553_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3552_, 1, v_x_3528_);
                        crate::leanh::lean_ctor_set(v___x_3552_, 0, v_x_3527_);
                        v___x_3558_ = v___x_3552_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_x_3527_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_x_3528_);
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
                    crate::leanh::lean_ctor_set(v___x_3563_, 0, v___x_3567_);
                    v___x_3569_ = v___x_3563_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
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
                    v_reuseFailAlloc_3595_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_ks_3575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_vs_3576_);
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
                    v___x_3593_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3594_ = lean_nat_dec_lt(v___x_3592_, v___x_3593_);
                    crate::leanh::lean_dec(v___x_3592_);
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
                    v_ks_3585_ = crate::leanh::lean_ctor_get(v_newNode_3582_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3585_);
                    v_vs_3586_ = crate::leanh::lean_ctor_get(v_newNode_3582_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3586_);
                    crate::leanh::lean_dec_ref(v_newNode_3582_);
                    v___x_3587_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___closed__2);
                    v___x_3589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_x_3526_, v_ks_3585_, v_vs_3586_, v___x_3587_, v___x_3588_);
                    crate::leanh::lean_dec_ref(v_vs_3586_);
                    crate::leanh::lean_dec_ref(v_ks_3585_);
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
    mut v_keys_3598_: *mut crate::leanh::LeanObject,
    mut v_vals_3599_: *mut crate::leanh::LeanObject,
    mut v_i_3600_: *mut crate::leanh::LeanObject,
    mut v_entries_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v_k_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: u64 = 0;
    let mut v_h_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: usize = 0;
    let mut v___x_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v_h_3613_: usize = 0;
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3602_ = lean_array_get_size(v_keys_3598_);
                v___x_3603_ = lean_nat_dec_lt(v_i_3600_, v___x_3602_);
                if v___x_3603_ == 0 {
                    crate::leanh::lean_dec(v_i_3600_);
                    return v_entries_3601_;
                } else {
                    v_k_3604_ = lean_array_fget_borrowed(v_keys_3598_, v_i_3600_);
                    v_v_3605_ = lean_array_fget_borrowed(v_vals_3599_, v_i_3600_);
                    v___x_3606_ = l_Lean_instHashableMVarId_hash(v_k_3604_);
                    v_h_3607_ = lean_uint64_to_usize(v___x_3606_);
                    v___x_3608_ = 5usize;
                    v___x_3609_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3610_ = 1usize;
                    v___x_3611_ = lean_usize_sub(v_depth_3597_, v___x_3610_);
                    v___x_3612_ = lean_usize_mul(v___x_3608_, v___x_3611_);
                    v_h_3613_ = lean_usize_shift_right(v_h_3607_, v___x_3612_);
                    v___x_3614_ = lean_nat_add(v_i_3600_, v___x_3609_);
                    crate::leanh::lean_dec(v_i_3600_);
                    crate::leanh::lean_inc(v_v_3605_);
                    crate::leanh::lean_inc(v_k_3604_);
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
    mut v_depth_3617_: *mut crate::leanh::LeanObject,
    mut v_keys_3618_: *mut crate::leanh::LeanObject,
    mut v_vals_3619_: *mut crate::leanh::LeanObject,
    mut v_i_3620_: *mut crate::leanh::LeanObject,
    mut v_entries_3621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3622_: usize = 0;
    let mut v_res_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3622_ = crate::leanh::lean_unbox_usize(v_depth_3617_);
    crate::leanh::lean_dec(v_depth_3617_);
    v_res_3623_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_boxed_3622_, v_keys_3618_, v_vals_3619_, v_i_3620_, v_entries_3621_);
    crate::leanh::lean_dec_ref(v_vals_3619_);
    crate::leanh::lean_dec_ref(v_keys_3618_);
    return v_res_3623_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_x_3624_: *mut crate::leanh::LeanObject,
    mut v_x_3625_: *mut crate::leanh::LeanObject,
    mut v_x_3626_: *mut crate::leanh::LeanObject,
    mut v_x_3627_: *mut crate::leanh::LeanObject,
    mut v_x_3628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3906__boxed_3629_: usize = 0;
    let mut v_x_3907__boxed_3630_: usize = 0;
    let mut v_res_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3906__boxed_3629_ = crate::leanh::lean_unbox_usize(v_x_3625_);
    crate::leanh::lean_dec(v_x_3625_);
    v_x_3907__boxed_3630_ = crate::leanh::lean_unbox_usize(v_x_3626_);
    crate::leanh::lean_dec(v_x_3626_);
    v_res_3631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_3624_, v_x_3906__boxed_3629_, v_x_3907__boxed_3630_, v_x_3627_, v_x_3628_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(
    mut v_x_3632_: *mut crate::leanh::LeanObject,
    mut v_x_3633_: *mut crate::leanh::LeanObject,
    mut v_x_3634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3635_: u64 = 0;
    let mut v___x_3636_: usize = 0;
    let mut v___x_3637_: usize = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3635_ = l_Lean_instHashableMVarId_hash(v_x_3633_);
    v___x_3636_ = lean_uint64_to_usize(v___x_3635_);
    v___x_3637_ = 1usize;
    v___x_3638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_3632_, v___x_3636_, v___x_3637_, v_x_3633_, v_x_3634_);
    return v___x_3638_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(
    mut v_mvarId_3639_: *mut crate::leanh::LeanObject,
    mut v_val_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v_depth_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3643_ = lean_st_ref_take(v___y_3641_);
                v_mctx_3644_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                v_cache_3645_ = crate::leanh::lean_ctor_get(v___x_3643_, 1);
                v_zetaDeltaFVarIds_3646_ = crate::leanh::lean_ctor_get(v___x_3643_, 2);
                v_postponed_3647_ = crate::leanh::lean_ctor_get(v___x_3643_, 3);
                v_diag_3648_ = crate::leanh::lean_ctor_get(v___x_3643_, 4);
                v_isSharedCheck_3676_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                if v_isSharedCheck_3676_ == 0 {
                    v___x_3650_ = v___x_3643_;
                    v_isShared_3651_ = v_isSharedCheck_3676_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3648_);
                    crate::leanh::lean_inc(v_postponed_3647_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3646_);
                    crate::leanh::lean_inc(v_cache_3645_);
                    crate::leanh::lean_inc(v_mctx_3644_);
                    crate::leanh::lean_dec(v___x_3643_);
                    v___x_3650_ = crate::leanh::lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3676_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3652_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 0);
                v_levelAssignDepth_3653_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 1);
                v_lmvarCounter_3654_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 2);
                v_mvarCounter_3655_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 3);
                v_lDecls_3656_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 4);
                v_decls_3657_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 5);
                v_userNames_3658_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 6);
                v_lAssignment_3659_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 7);
                v_eAssignment_3660_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 8);
                v_dAssignment_3661_ = crate::leanh::lean_ctor_get(v_mctx_3644_, 9);
                v_isSharedCheck_3675_ = (!crate::leanh::lean_is_exclusive(v_mctx_3644_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v___x_3663_ = v_mctx_3644_;
                    v_isShared_3664_ = v_isSharedCheck_3675_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_3661_);
                    crate::leanh::lean_inc(v_eAssignment_3660_);
                    crate::leanh::lean_inc(v_lAssignment_3659_);
                    crate::leanh::lean_inc(v_userNames_3658_);
                    crate::leanh::lean_inc(v_decls_3657_);
                    crate::leanh::lean_inc(v_lDecls_3656_);
                    crate::leanh::lean_inc(v_mvarCounter_3655_);
                    crate::leanh::lean_inc(v_lmvarCounter_3654_);
                    crate::leanh::lean_inc(v_levelAssignDepth_3653_);
                    crate::leanh::lean_inc(v_depth_3652_);
                    crate::leanh::lean_dec(v_mctx_3644_);
                    v___x_3663_ = crate::leanh::lean_box(0);
                    v_isShared_3664_ = v_isSharedCheck_3675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3665_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_eAssignment_3660_, v_mvarId_3639_, v_val_3640_);
                if v_isShared_3664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3663_, 8, v___x_3665_);
                    v___x_3667_ = v___x_3663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_depth_3652_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3674_,
                        1,
                        v_levelAssignDepth_3653_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_lmvarCounter_3654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_mvarCounter_3655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 4, v_lDecls_3656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 5, v_decls_3657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 6, v_userNames_3658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 7, v_lAssignment_3659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 8, v___x_3665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 9, v_dAssignment_3661_);
                    v___x_3667_ = v_reuseFailAlloc_3674_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3650_, 0, v___x_3667_);
                    v___x_3669_ = v___x_3650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_cache_3645_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3673_,
                        2,
                        v_zetaDeltaFVarIds_3646_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_postponed_3647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_diag_3648_);
                    v___x_3669_ = v_reuseFailAlloc_3673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3670_ = lean_st_ref_set(v___y_3641_, v___x_3669_);
                v___x_3671_ = crate::leanh::lean_box(0);
                v___x_3672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3672_, 0, v___x_3671_);
                return v___x_3672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg___boxed(
    mut v_mvarId_3677_: *mut crate::leanh::LeanObject,
    mut v_val_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_3677_, v_val_3678_, v___y_3679_);
    crate::leanh::lean_dec(v___y_3679_);
    return v_res_3681_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(
    mut v_mvarId_3682_: *mut crate::leanh::LeanObject,
    mut v_type_3683_: *mut crate::leanh::LeanObject,
    mut v_fvars_3684_: *mut crate::leanh::LeanObject,
    mut v_isZero_3685_: u8,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_unused_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v_a_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3722_: u8 = 0;
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3726_: u8 = 0;
    let mut v_a_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3734_: u8 = 0;
    let mut v_a_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3682_);
                v___x_3691_ = l_Lean_MVarId_getTag(
                    v_mvarId_3682_,
                    v___y_3686_,
                    v___y_3687_,
                    v___y_3688_,
                    v___y_3689_,
                );
                if crate::leanh::lean_obj_tag(v___x_3691_) == 0 {
                    v_a_3692_ = crate::leanh::lean_ctor_get(v___x_3691_, 0);
                    crate::leanh::lean_inc(v_a_3692_);
                    crate::leanh::lean_dec_ref_known(v___x_3691_, 1);
                    v___x_3693_ = l_Lean_Expr_headBeta(v_type_3683_);
                    v___x_3694_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_3693_,
                        v_a_3692_,
                        v___y_3686_,
                        v___y_3687_,
                        v___y_3688_,
                        v___y_3689_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3694_) == 0 {
                        v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                        crate::leanh::lean_inc_n(v_a_3695_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3694_, 1);
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
                        if crate::leanh::lean_obj_tag(v___x_3698_) == 0 {
                            v_a_3699_ = crate::leanh::lean_ctor_get(v___x_3698_, 0);
                            crate::leanh::lean_inc(v_a_3699_);
                            crate::leanh::lean_dec_ref_known(v___x_3698_, 1);
                            v___x_3700_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_3682_, v_a_3699_, v___y_3687_);
                            if crate::leanh::lean_obj_tag(v___x_3700_) == 0 {
                                v_isSharedCheck_3709_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3700_)) as u8;
                                if v_isSharedCheck_3709_ == 0 {
                                    v_unused_3710_ = crate::leanh::lean_ctor_get(v___x_3700_, 0);
                                    crate::leanh::lean_dec(v_unused_3710_);
                                    v___x_3702_ = v___x_3700_;
                                    v_isShared_3703_ = v_isSharedCheck_3709_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3700_);
                                    v___x_3702_ = crate::leanh::lean_box(0);
                                    v_isShared_3703_ = v_isSharedCheck_3709_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3695_);
                                crate::leanh::lean_dec_ref(v_fvars_3684_);
                                v_a_3711_ = crate::leanh::lean_ctor_get(v___x_3700_, 0);
                                v_isSharedCheck_3718_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3700_)) as u8;
                                if v_isSharedCheck_3718_ == 0 {
                                    v___x_3713_ = v___x_3700_;
                                    v_isShared_3714_ = v_isSharedCheck_3718_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3711_);
                                    crate::leanh::lean_dec(v___x_3700_);
                                    v___x_3713_ = crate::leanh::lean_box(0);
                                    v_isShared_3714_ = v_isSharedCheck_3718_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3695_);
                            crate::leanh::lean_dec_ref(v_fvars_3684_);
                            crate::leanh::lean_dec(v_mvarId_3682_);
                            v_a_3719_ = crate::leanh::lean_ctor_get(v___x_3698_, 0);
                            v_isSharedCheck_3726_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3698_)) as u8;
                            if v_isSharedCheck_3726_ == 0 {
                                v___x_3721_ = v___x_3698_;
                                v_isShared_3722_ = v_isSharedCheck_3726_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3719_);
                                crate::leanh::lean_dec(v___x_3698_);
                                v___x_3721_ = crate::leanh::lean_box(0);
                                v_isShared_3722_ = v_isSharedCheck_3726_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fvars_3684_);
                        crate::leanh::lean_dec(v_mvarId_3682_);
                        v_a_3727_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                        v_isSharedCheck_3734_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3694_)) as u8;
                        if v_isSharedCheck_3734_ == 0 {
                            v___x_3729_ = v___x_3694_;
                            v_isShared_3730_ = v_isSharedCheck_3734_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3727_);
                            crate::leanh::lean_dec(v___x_3694_);
                            v___x_3729_ = crate::leanh::lean_box(0);
                            v_isShared_3730_ = v_isSharedCheck_3734_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fvars_3684_);
                    crate::leanh::lean_dec_ref(v_type_3683_);
                    crate::leanh::lean_dec(v_mvarId_3682_);
                    v_a_3735_ = crate::leanh::lean_ctor_get(v___x_3691_, 0);
                    v_isSharedCheck_3742_ = (!crate::leanh::lean_is_exclusive(v___x_3691_)) as u8;
                    if v_isSharedCheck_3742_ == 0 {
                        v___x_3737_ = v___x_3691_;
                        v_isShared_3738_ = v_isSharedCheck_3742_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3735_);
                        crate::leanh::lean_dec(v___x_3691_);
                        v___x_3737_ = crate::leanh::lean_box(0);
                        v_isShared_3738_ = v_isSharedCheck_3742_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3704_ = l_Lean_Expr_mvarId_x21(v_a_3695_);
                crate::leanh::lean_dec(v_a_3695_);
                v___x_3705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3705_, 0, v_fvars_3684_);
                crate::leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
                if v_isShared_3703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3702_, 0, v___x_3705_);
                    v___x_3707_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
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
                    v_reuseFailAlloc_3717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
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
                    v_reuseFailAlloc_3725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
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
                    v_reuseFailAlloc_3733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
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
                    v_reuseFailAlloc_3741_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
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
    mut v_mvarId_3743_: *mut crate::leanh::LeanObject,
    mut v_type_3744_: *mut crate::leanh::LeanObject,
    mut v_fvars_3745_: *mut crate::leanh::LeanObject,
    mut v_isZero_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
    mut v___y_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isZero_boxed_3752_: u8 = 0;
    let mut v_res_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_3752_ = (crate::leanh::lean_unbox(v_isZero_3746_) as u8);
    v_res_3753_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0(v_mvarId_3743_, v_type_3744_, v_fvars_3745_, v_isZero_boxed_3752_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
    crate::leanh::lean_dec(v___y_3750_);
    crate::leanh::lean_dec_ref(v___y_3749_);
    crate::leanh::lean_dec(v___y_3748_);
    crate::leanh::lean_dec_ref(v___y_3747_);
    return v_res_3753_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(
    mut v_lctx_3754_: *mut crate::leanh::LeanObject,
    mut v_x_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyedConfig_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_3762_: u8 = 0;
    let mut v_zetaDeltaSet_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3768_: u8 = 0;
    let mut v_inTypeClassResolution_3769_: u8 = 0;
    let mut v_cacheInferType_3770_: u8 = 0;
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_3761_ = crate::leanh::lean_ctor_get(v___y_3756_, 0);
    v_trackZetaDelta_3762_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_3763_ = crate::leanh::lean_ctor_get(v___y_3756_, 1);
    v_localInstances_3764_ = crate::leanh::lean_ctor_get(v___y_3756_, 3);
    v_defEqCtx_x3f_3765_ = crate::leanh::lean_ctor_get(v___y_3756_, 4);
    v_synthPendingDepth_3766_ = crate::leanh::lean_ctor_get(v___y_3756_, 5);
    v_canUnfold_x3f_3767_ = crate::leanh::lean_ctor_get(v___y_3756_, 6);
    v_univApprox_3768_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_3769_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_3770_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3756_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
    );
    crate::leanh::lean_inc(v_canUnfold_x3f_3767_);
    crate::leanh::lean_inc(v_synthPendingDepth_3766_);
    crate::leanh::lean_inc(v_defEqCtx_x3f_3765_);
    crate::leanh::lean_inc_ref(v_localInstances_3764_);
    crate::leanh::lean_inc(v_zetaDeltaSet_3763_);
    crate::leanh::lean_inc_ref(v_keyedConfig_3761_);
    v___x_3771_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_3771_, 0, v_keyedConfig_3761_);
    crate::leanh::lean_ctor_set(v___x_3771_, 1, v_zetaDeltaSet_3763_);
    crate::leanh::lean_ctor_set(v___x_3771_, 2, v_lctx_3754_);
    crate::leanh::lean_ctor_set(v___x_3771_, 3, v_localInstances_3764_);
    crate::leanh::lean_ctor_set(v___x_3771_, 4, v_defEqCtx_x3f_3765_);
    crate::leanh::lean_ctor_set(v___x_3771_, 5, v_synthPendingDepth_3766_);
    crate::leanh::lean_ctor_set(v___x_3771_, 6, v_canUnfold_x3f_3767_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_3762_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_3768_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_3769_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3771_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_3770_,
    );
    crate::leanh::lean_inc(v___y_3759_);
    crate::leanh::lean_inc_ref(v___y_3758_);
    crate::leanh::lean_inc(v___y_3757_);
    v___x_3772_ = crate::leanh::lean_apply_5(
        v_x_3755_,
        v___x_3771_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
        crate::leanh::lean_box(0),
    );
    return v___x_3772_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg___boxed(
    mut v_lctx_3773_: *mut crate::leanh::LeanObject,
    mut v_x_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_3773_, v_x_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
    crate::leanh::lean_dec(v___y_3778_);
    crate::leanh::lean_dec_ref(v___y_3777_);
    crate::leanh::lean_dec(v___y_3776_);
    crate::leanh::lean_dec_ref(v___y_3775_);
    return v_res_3780_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed(
    mut v_type_3781_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3782_: *mut crate::leanh::LeanObject,
    mut v_n_3783_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_3784_: *mut crate::leanh::LeanObject,
    mut v___x_3785_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3786_: *mut crate::leanh::LeanObject,
    mut v_lctx_3787_: *mut crate::leanh::LeanObject,
    mut v_fvars_3788_: *mut crate::leanh::LeanObject,
    mut v___x_3789_: *mut crate::leanh::LeanObject,
    mut v_s_3790_: *mut crate::leanh::LeanObject,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3796_: u8 = 0;
    let mut v___x_4273__boxed_3797_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3798_: u8 = 0;
    let mut v_res_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3796_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_3784_) as u8);
    v___x_4273__boxed_3797_ = (crate::leanh::lean_unbox(v___x_3785_) as u8);
    v_useNamesForExplicitOnly_boxed_3798_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_3786_) as u8);
    v_res_3799_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1(v_type_3781_, v_mvarId_3782_, v_n_3783_, v_preserveBinderNames_boxed_3796_, v___x_4273__boxed_3797_, v_useNamesForExplicitOnly_boxed_3798_, v_lctx_3787_, v_fvars_3788_, v___x_3789_, v_s_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
    crate::leanh::lean_dec(v_n_3783_);
    return v_res_3799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(
    mut v_preserveBinderNames_3800_: u8,
    mut v___x_3801_: u8,
    mut v_useNamesForExplicitOnly_3802_: u8,
    mut v_mvarId_3803_: *mut crate::leanh::LeanObject,
    mut v_i_3804_: *mut crate::leanh::LeanObject,
    mut v_lctx_3805_: *mut crate::leanh::LeanObject,
    mut v_fvars_3806_: *mut crate::leanh::LeanObject,
    mut v_j_3807_: *mut crate::leanh::LeanObject,
    mut v_s_3808_: *mut crate::leanh::LeanObject,
    mut v_type_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3816_: u8 = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: u8 = 0;
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut v_a_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3856_: u8 = 0;
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3860_: u8 = 0;
    let mut v_binderName_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3864_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_a_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3815_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3816_ = lean_nat_dec_eq(v_i_3804_, v_zero_3815_);
                if v_isZero_3816_ == 1 {
                    crate::leanh::lean_dec(v_s_3808_);
                    crate::leanh::lean_dec(v_i_3804_);
                    v___x_3817_ = lean_array_get_size(v_fvars_3806_);
                    v_type_3818_ = lean_expr_instantiate_rev_range(
                        v_type_3809_,
                        v_j_3807_,
                        v___x_3817_,
                        v_fvars_3806_,
                    );
                    crate::leanh::lean_dec_ref(v_type_3809_);
                    v___x_3819_ = crate::leanh::lean_box((v_isZero_3816_) as usize);
                    crate::leanh::lean_inc_ref(v_fvars_3806_);
                    v___f_3820_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__0___boxed as *mut core::ffi::c_void, 9, 4);
                    crate::leanh::lean_closure_set(v___f_3820_, 0, v_mvarId_3803_);
                    crate::leanh::lean_closure_set(v___f_3820_, 1, v_type_3818_);
                    crate::leanh::lean_closure_set(v___f_3820_, 2, v_fvars_3806_);
                    crate::leanh::lean_closure_set(v___f_3820_, 3, v___x_3819_);
                    v___x_3821_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed as *mut core::ffi::c_void, 9, 4);
                    crate::leanh::lean_closure_set(v___x_3821_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3821_, 1, v_fvars_3806_);
                    crate::leanh::lean_closure_set(v___x_3821_, 2, v_j_3807_);
                    crate::leanh::lean_closure_set(v___x_3821_, 3, v___f_3820_);
                    v___x_3822_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_3805_, v___x_3821_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                    return v___x_3822_;
                } else {
                    v_one_3823_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3824_ = lean_nat_sub(v_i_3804_, v_one_3823_);
                    crate::leanh::lean_dec(v_i_3804_);
                    match crate::leanh::lean_obj_tag(v_type_3809_) {
                        8 => {
                            v_declName_3825_ = crate::leanh::lean_ctor_get(v_type_3809_, 0);
                            crate::leanh::lean_inc(v_declName_3825_);
                            v_type_3826_ = crate::leanh::lean_ctor_get(v_type_3809_, 1);
                            crate::leanh::lean_inc_ref(v_type_3826_);
                            v_value_3827_ = crate::leanh::lean_ctor_get(v_type_3809_, 2);
                            crate::leanh::lean_inc_ref(v_value_3827_);
                            v_body_3828_ = crate::leanh::lean_ctor_get(v_type_3809_, 3);
                            crate::leanh::lean_inc_ref(v_body_3828_);
                            crate::leanh::lean_dec_ref_known(v_type_3809_, 4);
                            v___x_3829_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                            if crate::leanh::lean_obj_tag(v___x_3829_) == 0 {
                                v_a_3830_ = crate::leanh::lean_ctor_get(v___x_3829_, 0);
                                crate::leanh::lean_inc(v_a_3830_);
                                crate::leanh::lean_dec_ref_known(v___x_3829_, 1);
                                v___x_3831_ = 1;
                                v___x_3832_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_3800_, v___x_3801_, v_useNamesForExplicitOnly_3802_, v_lctx_3805_, v_declName_3825_, v___x_3831_, v_s_3808_, v_a_3812_, v_a_3813_);
                                if crate::leanh::lean_obj_tag(v___x_3832_) == 0 {
                                    v_a_3833_ = crate::leanh::lean_ctor_get(v___x_3832_, 0);
                                    crate::leanh::lean_inc(v_a_3833_);
                                    crate::leanh::lean_dec_ref_known(v___x_3832_, 1);
                                    v_fst_3834_ = crate::leanh::lean_ctor_get(v_a_3833_, 0);
                                    crate::leanh::lean_inc(v_fst_3834_);
                                    v_snd_3835_ = crate::leanh::lean_ctor_get(v_a_3833_, 1);
                                    crate::leanh::lean_inc(v_snd_3835_);
                                    crate::leanh::lean_dec(v_a_3833_);
                                    v___x_3836_ = lean_array_get_size(v_fvars_3806_);
                                    v_type_3837_ = lean_expr_instantiate_rev_range(
                                        v_type_3826_,
                                        v_j_3807_,
                                        v___x_3836_,
                                        v_fvars_3806_,
                                    );
                                    crate::leanh::lean_dec_ref(v_type_3826_);
                                    v_type_3838_ = l_Lean_Expr_headBeta(v_type_3837_);
                                    v_val_3839_ = lean_expr_instantiate_rev_range(
                                        v_value_3827_,
                                        v_j_3807_,
                                        v___x_3836_,
                                        v_fvars_3806_,
                                    );
                                    crate::leanh::lean_dec_ref(v_value_3827_);
                                    v___x_3840_ = 0;
                                    crate::leanh::lean_inc(v_a_3830_);
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
                                    crate::leanh::lean_dec(v_a_3830_);
                                    crate::leanh::lean_dec_ref(v_body_3828_);
                                    crate::leanh::lean_dec_ref(v_value_3827_);
                                    crate::leanh::lean_dec_ref(v_type_3826_);
                                    crate::leanh::lean_dec(v_n_3824_);
                                    crate::leanh::lean_dec(v_j_3807_);
                                    crate::leanh::lean_dec_ref(v_fvars_3806_);
                                    crate::leanh::lean_dec_ref(v_lctx_3805_);
                                    crate::leanh::lean_dec(v_mvarId_3803_);
                                    v_a_3845_ = crate::leanh::lean_ctor_get(v___x_3832_, 0);
                                    v_isSharedCheck_3852_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3832_)) as u8;
                                    if v_isSharedCheck_3852_ == 0 {
                                        v___x_3847_ = v___x_3832_;
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3845_);
                                        crate::leanh::lean_dec(v___x_3832_);
                                        v___x_3847_ = crate::leanh::lean_box(0);
                                        v_isShared_3848_ = v_isSharedCheck_3852_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_3828_);
                                crate::leanh::lean_dec_ref(v_value_3827_);
                                crate::leanh::lean_dec_ref(v_type_3826_);
                                crate::leanh::lean_dec(v_declName_3825_);
                                crate::leanh::lean_dec(v_n_3824_);
                                crate::leanh::lean_dec(v_s_3808_);
                                crate::leanh::lean_dec(v_j_3807_);
                                crate::leanh::lean_dec_ref(v_fvars_3806_);
                                crate::leanh::lean_dec_ref(v_lctx_3805_);
                                crate::leanh::lean_dec(v_mvarId_3803_);
                                v_a_3853_ = crate::leanh::lean_ctor_get(v___x_3829_, 0);
                                v_isSharedCheck_3860_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3829_)) as u8;
                                if v_isSharedCheck_3860_ == 0 {
                                    v___x_3855_ = v___x_3829_;
                                    v_isShared_3856_ = v_isSharedCheck_3860_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3853_);
                                    crate::leanh::lean_dec(v___x_3829_);
                                    v___x_3855_ = crate::leanh::lean_box(0);
                                    v_isShared_3856_ = v_isSharedCheck_3860_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        7 => {
                            v_binderName_3861_ = crate::leanh::lean_ctor_get(v_type_3809_, 0);
                            crate::leanh::lean_inc(v_binderName_3861_);
                            v_binderType_3862_ = crate::leanh::lean_ctor_get(v_type_3809_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_3862_);
                            v_body_3863_ = crate::leanh::lean_ctor_get(v_type_3809_, 2);
                            crate::leanh::lean_inc_ref(v_body_3863_);
                            v_binderInfo_3864_ = crate::leanh::lean_ctor_get_uint8(
                                v_type_3809_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_type_3809_, 3);
                            v___x_3865_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3(v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
                            if crate::leanh::lean_obj_tag(v___x_3865_) == 0 {
                                v_a_3866_ = crate::leanh::lean_ctor_get(v___x_3865_, 0);
                                crate::leanh::lean_inc(v_a_3866_);
                                crate::leanh::lean_dec_ref_known(v___x_3865_, 1);
                                v___x_3867_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_3864_);
                                v___x_3868_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_mkAuxNameImp___redArg(v_preserveBinderNames_3800_, v___x_3801_, v_useNamesForExplicitOnly_3802_, v_lctx_3805_, v_binderName_3861_, v___x_3867_, v_s_3808_, v_a_3812_, v_a_3813_);
                                if crate::leanh::lean_obj_tag(v___x_3868_) == 0 {
                                    v_a_3869_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                                    crate::leanh::lean_inc(v_a_3869_);
                                    crate::leanh::lean_dec_ref_known(v___x_3868_, 1);
                                    v_fst_3870_ = crate::leanh::lean_ctor_get(v_a_3869_, 0);
                                    crate::leanh::lean_inc(v_fst_3870_);
                                    v_snd_3871_ = crate::leanh::lean_ctor_get(v_a_3869_, 1);
                                    crate::leanh::lean_inc(v_snd_3871_);
                                    crate::leanh::lean_dec(v_a_3869_);
                                    v___x_3872_ = lean_array_get_size(v_fvars_3806_);
                                    v_type_3873_ = lean_expr_instantiate_rev_range(
                                        v_binderType_3862_,
                                        v_j_3807_,
                                        v___x_3872_,
                                        v_fvars_3806_,
                                    );
                                    crate::leanh::lean_dec_ref(v_binderType_3862_);
                                    v_type_3874_ = l_Lean_Expr_headBeta(v_type_3873_);
                                    v___x_3875_ = 0;
                                    crate::leanh::lean_inc(v_a_3866_);
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
                                    crate::leanh::lean_dec(v_a_3866_);
                                    crate::leanh::lean_dec_ref(v_body_3863_);
                                    crate::leanh::lean_dec_ref(v_binderType_3862_);
                                    crate::leanh::lean_dec(v_n_3824_);
                                    crate::leanh::lean_dec(v_j_3807_);
                                    crate::leanh::lean_dec_ref(v_fvars_3806_);
                                    crate::leanh::lean_dec_ref(v_lctx_3805_);
                                    crate::leanh::lean_dec(v_mvarId_3803_);
                                    v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                                    v_isSharedCheck_3887_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3868_)) as u8;
                                    if v_isSharedCheck_3887_ == 0 {
                                        v___x_3882_ = v___x_3868_;
                                        v_isShared_3883_ = v_isSharedCheck_3887_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3880_);
                                        crate::leanh::lean_dec(v___x_3868_);
                                        v___x_3882_ = crate::leanh::lean_box(0);
                                        v_isShared_3883_ = v_isSharedCheck_3887_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_3863_);
                                crate::leanh::lean_dec_ref(v_binderType_3862_);
                                crate::leanh::lean_dec(v_binderName_3861_);
                                crate::leanh::lean_dec(v_n_3824_);
                                crate::leanh::lean_dec(v_s_3808_);
                                crate::leanh::lean_dec(v_j_3807_);
                                crate::leanh::lean_dec_ref(v_fvars_3806_);
                                crate::leanh::lean_dec_ref(v_lctx_3805_);
                                crate::leanh::lean_dec(v_mvarId_3803_);
                                v_a_3888_ = crate::leanh::lean_ctor_get(v___x_3865_, 0);
                                v_isSharedCheck_3895_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3865_)) as u8;
                                if v_isSharedCheck_3895_ == 0 {
                                    v___x_3890_ = v___x_3865_;
                                    v_isShared_3891_ = v_isSharedCheck_3895_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3888_);
                                    crate::leanh::lean_dec(v___x_3865_);
                                    v___x_3890_ = crate::leanh::lean_box(0);
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
                            crate::leanh::lean_dec_ref(v_type_3809_);
                            v___x_3898_ =
                                crate::leanh::lean_box((v_preserveBinderNames_3800_) as usize);
                            v___x_3899_ = crate::leanh::lean_box((v___x_3801_) as usize);
                            v___x_3900_ =
                                crate::leanh::lean_box((v_useNamesForExplicitOnly_3802_) as usize);
                            crate::leanh::lean_inc_ref(v_fvars_3806_);
                            crate::leanh::lean_inc_ref(v_lctx_3805_);
                            v___f_3901_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0___lam__1___boxed as *mut core::ffi::c_void, 15, 10);
                            crate::leanh::lean_closure_set(v___f_3901_, 0, v_type_3897_);
                            crate::leanh::lean_closure_set(v___f_3901_, 1, v_mvarId_3803_);
                            crate::leanh::lean_closure_set(v___f_3901_, 2, v_n_3824_);
                            crate::leanh::lean_closure_set(v___f_3901_, 3, v___x_3898_);
                            crate::leanh::lean_closure_set(v___f_3901_, 4, v___x_3899_);
                            crate::leanh::lean_closure_set(v___f_3901_, 5, v___x_3900_);
                            crate::leanh::lean_closure_set(v___f_3901_, 6, v_lctx_3805_);
                            crate::leanh::lean_closure_set(v___f_3901_, 7, v_fvars_3806_);
                            crate::leanh::lean_closure_set(v___f_3901_, 8, v___x_3896_);
                            crate::leanh::lean_closure_set(v___f_3901_, 9, v_s_3808_);
                            v___x_3902_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1___boxed as *mut core::ffi::c_void, 9, 4);
                            crate::leanh::lean_closure_set(
                                v___x_3902_,
                                0,
                                crate::leanh::lean_box(0),
                            );
                            crate::leanh::lean_closure_set(v___x_3902_, 1, v_fvars_3806_);
                            crate::leanh::lean_closure_set(v___x_3902_, 2, v_j_3807_);
                            crate::leanh::lean_closure_set(v___x_3902_, 3, v___f_3901_);
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
                    v_reuseFailAlloc_3851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
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
                    v_reuseFailAlloc_3859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
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
                    v_reuseFailAlloc_3886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
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
                    v_reuseFailAlloc_3894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
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
    mut v_type_3904_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3905_: *mut crate::leanh::LeanObject,
    mut v_n_3906_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_3907_: u8,
    mut v___x_3908_: u8,
    mut v_useNamesForExplicitOnly_3909_: u8,
    mut v_lctx_3910_: *mut crate::leanh::LeanObject,
    mut v_fvars_3911_: *mut crate::leanh::LeanObject,
    mut v___x_3912_: *mut crate::leanh::LeanObject,
    mut v_s_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3936_: u8 = 0;
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u8 = 0;
    let mut v___x_3945_: u8 = 0;
    let mut v_a_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3949_: u8 = 0;
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3919_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_type_3904_, v___y_3915_);
                if crate::leanh::lean_obj_tag(v___x_3919_) == 0 {
                    v_a_3920_ = crate::leanh::lean_ctor_get(v___x_3919_, 0);
                    crate::leanh::lean_inc(v_a_3920_);
                    crate::leanh::lean_dec_ref_known(v___x_3919_, 1);
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
                    crate::leanh::lean_dec(v___y_3917_);
                    crate::leanh::lean_dec_ref(v___y_3916_);
                    crate::leanh::lean_dec(v___y_3915_);
                    crate::leanh::lean_dec_ref(v___y_3914_);
                    crate::leanh::lean_dec(v_s_3913_);
                    crate::leanh::lean_dec(v___x_3912_);
                    crate::leanh::lean_dec_ref(v_fvars_3911_);
                    crate::leanh::lean_dec_ref(v_lctx_3910_);
                    crate::leanh::lean_dec(v_mvarId_3905_);
                    v_a_3946_ = crate::leanh::lean_ctor_get(v___x_3919_, 0);
                    v_isSharedCheck_3953_ = (!crate::leanh::lean_is_exclusive(v___x_3919_)) as u8;
                    if v_isSharedCheck_3953_ == 0 {
                        v___x_3948_ = v___x_3919_;
                        v_isShared_3949_ = v_isSharedCheck_3953_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3946_);
                        crate::leanh::lean_dec(v___x_3919_);
                        v___x_3948_ = crate::leanh::lean_box(0);
                        v_isShared_3949_ = v_isSharedCheck_3953_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3923_ == 0 {
                    crate::leanh::lean_inc(v___y_3917_);
                    crate::leanh::lean_inc_ref(v___y_3916_);
                    crate::leanh::lean_inc(v___y_3915_);
                    crate::leanh::lean_inc_ref(v___y_3914_);
                    v___x_3924_ = lean_whnf(
                        v___x_3921_,
                        v___y_3914_,
                        v___y_3915_,
                        v___y_3916_,
                        v___y_3917_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3924_) == 0 {
                        v_a_3925_ = crate::leanh::lean_ctor_get(v___x_3924_, 0);
                        crate::leanh::lean_inc(v_a_3925_);
                        crate::leanh::lean_dec_ref_known(v___x_3924_, 1);
                        v___x_3926_ = l_Lean_Expr_isForall(v_a_3925_);
                        if v___x_3926_ == 0 {
                            crate::leanh::lean_dec(v_a_3925_);
                            crate::leanh::lean_dec(v_s_3913_);
                            crate::leanh::lean_dec(v___x_3912_);
                            crate::leanh::lean_dec_ref(v_fvars_3911_);
                            crate::leanh::lean_dec_ref(v_lctx_3910_);
                            v___x_3927_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
                            v___x_3928_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4_once), _init_l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__4);
                            v___x_3929_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_3927_,
                                v_mvarId_3905_,
                                v___x_3928_,
                                v___y_3914_,
                                v___y_3915_,
                                v___y_3916_,
                                v___y_3917_,
                            );
                            crate::leanh::lean_dec(v___y_3917_);
                            crate::leanh::lean_dec_ref(v___y_3916_);
                            crate::leanh::lean_dec(v___y_3915_);
                            crate::leanh::lean_dec_ref(v___y_3914_);
                            return v___x_3929_;
                        } else {
                            v___x_3930_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3931_ = lean_nat_add(v_n_3906_, v___x_3930_);
                            v___x_3932_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_3907_, v___x_3908_, v_useNamesForExplicitOnly_3909_, v_mvarId_3905_, v___x_3931_, v_lctx_3910_, v_fvars_3911_, v___x_3912_, v_s_3913_, v_a_3925_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                            crate::leanh::lean_dec(v___y_3917_);
                            crate::leanh::lean_dec_ref(v___y_3916_);
                            crate::leanh::lean_dec(v___y_3915_);
                            crate::leanh::lean_dec_ref(v___y_3914_);
                            return v___x_3932_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3917_);
                        crate::leanh::lean_dec_ref(v___y_3916_);
                        crate::leanh::lean_dec(v___y_3915_);
                        crate::leanh::lean_dec_ref(v___y_3914_);
                        crate::leanh::lean_dec(v_s_3913_);
                        crate::leanh::lean_dec(v___x_3912_);
                        crate::leanh::lean_dec_ref(v_fvars_3911_);
                        crate::leanh::lean_dec_ref(v_lctx_3910_);
                        crate::leanh::lean_dec(v_mvarId_3905_);
                        v_a_3933_ = crate::leanh::lean_ctor_get(v___x_3924_, 0);
                        v_isSharedCheck_3940_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3924_)) as u8;
                        if v_isSharedCheck_3940_ == 0 {
                            v___x_3935_ = v___x_3924_;
                            v_isShared_3936_ = v_isSharedCheck_3940_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3933_);
                            crate::leanh::lean_dec(v___x_3924_);
                            v___x_3935_ = crate::leanh::lean_box(0);
                            v_isShared_3936_ = v_isSharedCheck_3940_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3941_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3942_ = lean_nat_add(v_n_3906_, v___x_3941_);
                    v___x_3943_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_3907_, v___x_3908_, v_useNamesForExplicitOnly_3909_, v_mvarId_3905_, v___x_3942_, v_lctx_3910_, v_fvars_3911_, v___x_3912_, v_s_3913_, v___x_3921_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                    crate::leanh::lean_dec(v___y_3917_);
                    crate::leanh::lean_dec_ref(v___y_3916_);
                    crate::leanh::lean_dec(v___y_3915_);
                    crate::leanh::lean_dec_ref(v___y_3914_);
                    return v___x_3943_;
                }
            }
            2 => {
                if v_isShared_3936_ == 0 {
                    v___x_3938_ = v___x_3935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
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
                    v_reuseFailAlloc_3952_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
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
    mut v_preserveBinderNames_3954_: *mut crate::leanh::LeanObject,
    mut v___x_3955_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_3956_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3957_: *mut crate::leanh::LeanObject,
    mut v_i_3958_: *mut crate::leanh::LeanObject,
    mut v_lctx_3959_: *mut crate::leanh::LeanObject,
    mut v_fvars_3960_: *mut crate::leanh::LeanObject,
    mut v_j_3961_: *mut crate::leanh::LeanObject,
    mut v_s_3962_: *mut crate::leanh::LeanObject,
    mut v_type_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_3969_: u8 = 0;
    let mut v___x_4306__boxed_3970_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_3971_: u8 = 0;
    let mut v_res_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_3969_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_3954_) as u8);
    v___x_4306__boxed_3970_ = (crate::leanh::lean_unbox(v___x_3955_) as u8);
    v_useNamesForExplicitOnly_boxed_3971_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_3956_) as u8);
    v_res_3972_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_boxed_3969_, v___x_4306__boxed_3970_, v_useNamesForExplicitOnly_boxed_3971_, v_mvarId_3957_, v_i_3958_, v_lctx_3959_, v_fvars_3960_, v_j_3961_, v_s_3962_, v_type_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
    crate::leanh::lean_dec(v_a_3967_);
    crate::leanh::lean_dec_ref(v_a_3966_);
    crate::leanh::lean_dec(v_a_3965_);
    crate::leanh::lean_dec_ref(v_a_3964_);
    return v_res_3972_;
}
pub unsafe fn l_Lean_Meta_introNCore___lam__0(
    mut v_mvarId_3973_: *mut crate::leanh::LeanObject,
    mut v___x_3974_: *mut crate::leanh::LeanObject,
    mut v___x_3975_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_3976_: u8,
    mut v___x_3977_: u8,
    mut v_useNamesForExplicitOnly_3978_: u8,
    mut v_n_3979_: *mut crate::leanh::LeanObject,
    mut v_givenNames_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v_fst_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_sz_4001_: usize = 0;
    let mut v___x_4002_: usize = 0;
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4010_: u8 = 0;
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v_a_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_a_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut v_a_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3973_);
                v___x_3986_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_3973_,
                    v___x_3974_,
                    v___y_3981_,
                    v___y_3982_,
                    v___y_3983_,
                    v___y_3984_,
                );
                if crate::leanh::lean_obj_tag(v___x_3986_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3986_, 1);
                    crate::leanh::lean_inc(v_mvarId_3973_);
                    v___x_3987_ = l_Lean_MVarId_getType(
                        v_mvarId_3973_,
                        v___y_3981_,
                        v___y_3982_,
                        v___y_3983_,
                        v___y_3984_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3987_) == 0 {
                        v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                        crate::leanh::lean_inc(v_a_3988_);
                        crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                        v_lctx_3989_ = crate::leanh::lean_ctor_get(v___y_3981_, 2);
                        crate::leanh::lean_inc_ref(v_lctx_3989_);
                        v___x_3990_ = lean_mk_empty_array_with_capacity(v___x_3975_);
                        v___x_3991_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0(v_preserveBinderNames_3976_, v___x_3977_, v_useNamesForExplicitOnly_3978_, v_mvarId_3973_, v_n_3979_, v_lctx_3989_, v___x_3990_, v___x_3975_, v_givenNames_3980_, v_a_3988_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
                        crate::leanh::lean_dec_ref(v___y_3981_);
                        if crate::leanh::lean_obj_tag(v___x_3991_) == 0 {
                            v_a_3992_ = crate::leanh::lean_ctor_get(v___x_3991_, 0);
                            v_isSharedCheck_4011_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3991_)) as u8;
                            if v_isSharedCheck_4011_ == 0 {
                                v___x_3994_ = v___x_3991_;
                                v_isShared_3995_ = v_isSharedCheck_4011_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3992_);
                                crate::leanh::lean_dec(v___x_3991_);
                                v___x_3994_ = crate::leanh::lean_box(0);
                                v_isShared_3995_ = v_isSharedCheck_4011_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4012_ = crate::leanh::lean_ctor_get(v___x_3991_, 0);
                            v_isSharedCheck_4019_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3991_)) as u8;
                            if v_isSharedCheck_4019_ == 0 {
                                v___x_4014_ = v___x_3991_;
                                v_isShared_4015_ = v_isSharedCheck_4019_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4012_);
                                crate::leanh::lean_dec(v___x_3991_);
                                v___x_4014_ = crate::leanh::lean_box(0);
                                v_isShared_4015_ = v_isSharedCheck_4019_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3981_);
                        crate::leanh::lean_dec(v_givenNames_3980_);
                        crate::leanh::lean_dec(v_n_3979_);
                        crate::leanh::lean_dec(v___x_3975_);
                        crate::leanh::lean_dec(v_mvarId_3973_);
                        v_a_4020_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                        v_isSharedCheck_4027_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3987_)) as u8;
                        if v_isSharedCheck_4027_ == 0 {
                            v___x_4022_ = v___x_3987_;
                            v_isShared_4023_ = v_isSharedCheck_4027_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4020_);
                            crate::leanh::lean_dec(v___x_3987_);
                            v___x_4022_ = crate::leanh::lean_box(0);
                            v_isShared_4023_ = v_isSharedCheck_4027_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3981_);
                    crate::leanh::lean_dec(v_givenNames_3980_);
                    crate::leanh::lean_dec(v_n_3979_);
                    crate::leanh::lean_dec(v___x_3975_);
                    crate::leanh::lean_dec(v_mvarId_3973_);
                    v_a_4028_ = crate::leanh::lean_ctor_get(v___x_3986_, 0);
                    v_isSharedCheck_4035_ = (!crate::leanh::lean_is_exclusive(v___x_3986_)) as u8;
                    if v_isSharedCheck_4035_ == 0 {
                        v___x_4030_ = v___x_3986_;
                        v_isShared_4031_ = v_isSharedCheck_4035_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4028_);
                        crate::leanh::lean_dec(v___x_3986_);
                        v___x_4030_ = crate::leanh::lean_box(0);
                        v_isShared_4031_ = v_isSharedCheck_4035_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3996_ = crate::leanh::lean_ctor_get(v_a_3992_, 0);
                v_snd_3997_ = crate::leanh::lean_ctor_get(v_a_3992_, 1);
                v_isSharedCheck_4010_ = (!crate::leanh::lean_is_exclusive(v_a_3992_)) as u8;
                if v_isSharedCheck_4010_ == 0 {
                    v___x_3999_ = v_a_3992_;
                    v_isShared_4000_ = v_isSharedCheck_4010_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3997_);
                    crate::leanh::lean_inc(v_fst_3996_);
                    crate::leanh::lean_dec(v_a_3992_);
                    v___x_3999_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_3999_, 0, v___x_4003_);
                    v___x_4005_ = v___x_3999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4009_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 1, v_snd_3997_);
                    v___x_4005_ = v_reuseFailAlloc_4009_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3995_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3994_, 0, v___x_4005_);
                    v___x_4007_ = v___x_3994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
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
                    v_reuseFailAlloc_4018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
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
                    v_reuseFailAlloc_4026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
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
                    v_reuseFailAlloc_4034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
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
    mut v_mvarId_4036_: *mut crate::leanh::LeanObject,
    mut v___x_4037_: *mut crate::leanh::LeanObject,
    mut v___x_4038_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_4039_: *mut crate::leanh::LeanObject,
    mut v___x_4040_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4041_: *mut crate::leanh::LeanObject,
    mut v_n_4042_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_4049_: u8 = 0;
    let mut v___x_4536__boxed_4050_: u8 = 0;
    let mut v_useNamesForExplicitOnly_boxed_4051_: u8 = 0;
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_4049_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_4039_) as u8);
    v___x_4536__boxed_4050_ = (crate::leanh::lean_unbox(v___x_4040_) as u8);
    v_useNamesForExplicitOnly_boxed_4051_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_4041_) as u8);
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
    crate::leanh::lean_dec(v___y_4047_);
    crate::leanh::lean_dec_ref(v___y_4046_);
    crate::leanh::lean_dec(v___y_4045_);
    return v_res_4052_;
}
pub unsafe fn l_Lean_Meta_introNCore(
    mut v_mvarId_4055_: *mut crate::leanh::LeanObject,
    mut v_n_4056_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4057_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4058_: u8,
    mut v_preserveBinderNames_4059_: u8,
    mut v_a_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    v___x_4065_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4066_ = lean_nat_dec_eq(v_n_4056_, v___x_4065_);
    if v___x_4066_ == 0 {
        let mut v_options_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: u8 = 0;
        let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_options_4067_ = crate::leanh::lean_ctor_get(v_a_4062_, 2);
        v___x_4068_ = l_Lean_Meta_tactic_hygienic;
        v___x_4069_ = l_Lean_Option_get___at___00Lean_Meta_mkFreshBinderNameForTactic_spec__0(
            v_options_4067_,
            v___x_4068_,
        );
        v___x_4070_ = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___redArg___lam__1___closed__1;
        v___x_4071_ = crate::leanh::lean_box((v_preserveBinderNames_4059_) as usize);
        v___x_4072_ = crate::leanh::lean_box((v___x_4069_) as usize);
        v___x_4073_ = crate::leanh::lean_box((v_useNamesForExplicitOnly_4058_) as usize);
        crate::leanh::lean_inc(v_mvarId_4055_);
        v___f_4074_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_introNCore___lam__0___boxed as *mut core::ffi::c_void,
            13,
            8,
        );
        crate::leanh::lean_closure_set(v___f_4074_, 0, v_mvarId_4055_);
        crate::leanh::lean_closure_set(v___f_4074_, 1, v___x_4070_);
        crate::leanh::lean_closure_set(v___f_4074_, 2, v___x_4065_);
        crate::leanh::lean_closure_set(v___f_4074_, 3, v___x_4071_);
        crate::leanh::lean_closure_set(v___f_4074_, 4, v___x_4072_);
        crate::leanh::lean_closure_set(v___f_4074_, 5, v___x_4073_);
        crate::leanh::lean_closure_set(v___f_4074_, 6, v_n_4056_);
        crate::leanh::lean_closure_set(v___f_4074_, 7, v_givenNames_4057_);
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
        let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_givenNames_4057_);
        crate::leanh::lean_dec(v_n_4056_);
        v___x_4076_ = l_Lean_Meta_introNCore___closed__0;
        v___x_4077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4077_, 0, v___x_4076_);
        crate::leanh::lean_ctor_set(v___x_4077_, 1, v_mvarId_4055_);
        v___x_4078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4078_, 0, v___x_4077_);
        return v___x_4078_;
    }
}
pub unsafe fn l_Lean_Meta_introNCore___boxed(
    mut v_mvarId_4079_: *mut crate::leanh::LeanObject,
    mut v_n_4080_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4081_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4082_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useNamesForExplicitOnly_boxed_4089_: u8 = 0;
    let mut v_preserveBinderNames_boxed_4090_: u8 = 0;
    let mut v_res_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useNamesForExplicitOnly_boxed_4089_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_4082_) as u8);
    v_preserveBinderNames_boxed_4090_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_4083_) as u8);
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
    crate::leanh::lean_dec(v_a_4087_);
    crate::leanh::lean_dec_ref(v_a_4086_);
    crate::leanh::lean_dec(v_a_4085_);
    crate::leanh::lean_dec_ref(v_a_4084_);
    return v_res_4091_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(
    mut v_00_u03b1_4092_: *mut crate::leanh::LeanObject,
    mut v_lctx_4093_: *mut crate::leanh::LeanObject,
    mut v_x_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4100_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___redArg(v_lctx_4093_, v_x_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
    return v___x_4100_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2___boxed(
    mut v_00_u03b1_4101_: *mut crate::leanh::LeanObject,
    mut v_lctx_4102_: *mut crate::leanh::LeanObject,
    mut v_x_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__2(v_00_u03b1_4101_, v_lctx_4102_, v_x_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
    crate::leanh::lean_dec(v___y_4107_);
    crate::leanh::lean_dec_ref(v___y_4106_);
    crate::leanh::lean_dec(v___y_4105_);
    crate::leanh::lean_dec_ref(v___y_4104_);
    return v_res_4109_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(
    mut v_e_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4116_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_e_4110_, v___y_4112_);
    return v___x_4116_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___boxed(
    mut v_e_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4(v_e_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
    crate::leanh::lean_dec(v___y_4121_);
    crate::leanh::lean_dec_ref(v___y_4120_);
    crate::leanh::lean_dec(v___y_4119_);
    crate::leanh::lean_dec_ref(v___y_4118_);
    return v_res_4123_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(
    mut v_mvarId_4124_: *mut crate::leanh::LeanObject,
    mut v_val_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_4124_, v_val_4125_, v___y_4127_);
    return v___x_4131_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___boxed(
    mut v_mvarId_4132_: *mut crate::leanh::LeanObject,
    mut v_val_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4139_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0(v_mvarId_4132_, v_val_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
    crate::leanh::lean_dec(v___y_4137_);
    crate::leanh::lean_dec_ref(v___y_4136_);
    crate::leanh::lean_dec(v___y_4135_);
    crate::leanh::lean_dec_ref(v___y_4134_);
    return v_res_4139_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4140_: *mut crate::leanh::LeanObject,
    mut v_fvars_4141_: *mut crate::leanh::LeanObject,
    mut v_j_4142_: *mut crate::leanh::LeanObject,
    mut v_x_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___redArg(v_fvars_4141_, v_j_4142_, v_x_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
    return v___x_4149_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_4150_: *mut crate::leanh::LeanObject,
    mut v_fvars_4151_: *mut crate::leanh::LeanObject,
    mut v_j_4152_: *mut crate::leanh::LeanObject,
    mut v_x_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
    mut v___y_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImpAux___at___00Lean_Meta_withNewLocalInstances___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__1_spec__4(v_00_u03b1_4150_, v_fvars_4151_, v_j_4152_, v_x_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
    crate::leanh::lean_dec(v___y_4157_);
    crate::leanh::lean_dec_ref(v___y_4156_);
    crate::leanh::lean_dec(v___y_4155_);
    crate::leanh::lean_dec_ref(v___y_4154_);
    return v_res_4159_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___redArg(v___y_4163_);
    return v___x_4165_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7___boxed(
    mut v___y_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__3_spec__7(v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
    crate::leanh::lean_dec(v___y_4169_);
    crate::leanh::lean_dec_ref(v___y_4168_);
    crate::leanh::lean_dec(v___y_4167_);
    crate::leanh::lean_dec_ref(v___y_4166_);
    return v_res_4171_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4172_: *mut crate::leanh::LeanObject,
    mut v_x_4173_: *mut crate::leanh::LeanObject,
    mut v_x_4174_: *mut crate::leanh::LeanObject,
    mut v_x_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2___redArg(v_x_4173_, v_x_4174_, v_x_4175_);
    return v___x_4176_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_4177_: *mut crate::leanh::LeanObject,
    mut v_x_4178_: *mut crate::leanh::LeanObject,
    mut v_x_4179_: usize,
    mut v_x_4180_: usize,
    mut v_x_4181_: *mut crate::leanh::LeanObject,
    mut v_x_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_4178_, v_x_4179_, v_x_4180_, v_x_4181_, v_x_4182_);
    return v___x_4183_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_4184_: *mut crate::leanh::LeanObject,
    mut v_x_4185_: *mut crate::leanh::LeanObject,
    mut v_x_4186_: *mut crate::leanh::LeanObject,
    mut v_x_4187_: *mut crate::leanh::LeanObject,
    mut v_x_4188_: *mut crate::leanh::LeanObject,
    mut v_x_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4787__boxed_4190_: usize = 0;
    let mut v_x_4788__boxed_4191_: usize = 0;
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4787__boxed_4190_ = crate::leanh::lean_unbox_usize(v_x_4186_);
    crate::leanh::lean_dec(v_x_4186_);
    v_x_4788__boxed_4191_ = crate::leanh::lean_unbox_usize(v_x_4187_);
    crate::leanh::lean_dec(v_x_4187_);
    v_res_4192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_4184_, v_x_4185_, v_x_4787__boxed_4190_, v_x_4788__boxed_4191_, v_x_4188_, v_x_4189_);
    return v_res_4192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11(
    mut v_00_u03b2_4193_: *mut crate::leanh::LeanObject,
    mut v_n_4194_: *mut crate::leanh::LeanObject,
    mut v_k_4195_: *mut crate::leanh::LeanObject,
    mut v_v_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4197_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11___redArg(v_n_4194_, v_k_4195_, v_v_4196_);
    return v___x_4197_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(
    mut v_00_u03b2_4198_: *mut crate::leanh::LeanObject,
    mut v_depth_4199_: usize,
    mut v_keys_4200_: *mut crate::leanh::LeanObject,
    mut v_vals_4201_: *mut crate::leanh::LeanObject,
    mut v_heq_4202_: *mut crate::leanh::LeanObject,
    mut v_i_4203_: *mut crate::leanh::LeanObject,
    mut v_entries_4204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4205_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___redArg(v_depth_4199_, v_keys_4200_, v_vals_4201_, v_i_4203_, v_entries_4204_);
    return v___x_4205_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_00_u03b2_4206_: *mut crate::leanh::LeanObject,
    mut v_depth_4207_: *mut crate::leanh::LeanObject,
    mut v_keys_4208_: *mut crate::leanh::LeanObject,
    mut v_vals_4209_: *mut crate::leanh::LeanObject,
    mut v_heq_4210_: *mut crate::leanh::LeanObject,
    mut v_i_4211_: *mut crate::leanh::LeanObject,
    mut v_entries_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4213_: usize = 0;
    let mut v_res_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4213_ = crate::leanh::lean_unbox_usize(v_depth_4207_);
    crate::leanh::lean_dec(v_depth_4207_);
    v_res_4214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_4206_, v_depth_boxed_4213_, v_keys_4208_, v_vals_4209_, v_heq_4210_, v_i_4211_, v_entries_4212_);
    crate::leanh::lean_dec_ref(v_vals_4209_);
    crate::leanh::lean_dec_ref(v_keys_4208_);
    return v_res_4214_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12(
    mut v_00_u03b2_4215_: *mut crate::leanh::LeanObject,
    mut v_x_4216_: *mut crate::leanh::LeanObject,
    mut v_x_4217_: *mut crate::leanh::LeanObject,
    mut v_x_4218_: *mut crate::leanh::LeanObject,
    mut v_x_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0_spec__2_spec__6_spec__11_spec__12___redArg(v_x_4216_, v_x_4217_, v_x_4218_, v_x_4219_);
    return v___x_4220_;
}
pub unsafe fn l_Lean_MVarId_introN(
    mut v_mvarId_4221_: *mut crate::leanh::LeanObject,
    mut v_n_4222_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4223_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4224_: u8,
    mut v_a_4225_: *mut crate::leanh::LeanObject,
    mut v_a_4226_: *mut crate::leanh::LeanObject,
    mut v_a_4227_: *mut crate::leanh::LeanObject,
    mut v_a_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: u8 = 0;
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_4232_: *mut crate::leanh::LeanObject,
    mut v_n_4233_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4234_: *mut crate::leanh::LeanObject,
    mut v_useNamesForExplicitOnly_4235_: *mut crate::leanh::LeanObject,
    mut v_a_4236_: *mut crate::leanh::LeanObject,
    mut v_a_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useNamesForExplicitOnly_boxed_4241_: u8 = 0;
    let mut v_res_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useNamesForExplicitOnly_boxed_4241_ =
        (crate::leanh::lean_unbox(v_useNamesForExplicitOnly_4235_) as u8);
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
    crate::leanh::lean_dec(v_a_4239_);
    crate::leanh::lean_dec_ref(v_a_4238_);
    crate::leanh::lean_dec(v_a_4237_);
    crate::leanh::lean_dec_ref(v_a_4236_);
    return v_res_4242_;
}
pub unsafe fn l_Lean_MVarId_introNP(
    mut v_mvarId_4243_: *mut crate::leanh::LeanObject,
    mut v_n_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = crate::leanh::lean_box(0);
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
    mut v_mvarId_4254_: *mut crate::leanh::LeanObject,
    mut v_n_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
    mut v_a_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4261_ = l_Lean_MVarId_introNP(
        v_mvarId_4254_,
        v_n_4255_,
        v_a_4256_,
        v_a_4257_,
        v_a_4258_,
        v_a_4259_,
    );
    crate::leanh::lean_dec(v_a_4259_);
    crate::leanh::lean_dec_ref(v_a_4258_);
    crate::leanh::lean_dec(v_a_4257_);
    crate::leanh::lean_dec_ref(v_a_4256_);
    return v_res_4261_;
}
pub unsafe fn l_Lean_MVarId_intro(
    mut v_mvarId_4262_: *mut crate::leanh::LeanObject,
    mut v_name_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v_fst_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4282_: u8 = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut v_a_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4269_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4270_ = crate::leanh::lean_box(0);
                v___x_4271_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4271_, 0, v_name_4263_);
                crate::leanh::lean_ctor_set(v___x_4271_, 1, v___x_4270_);
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
                if crate::leanh::lean_obj_tag(v___x_4273_) == 0 {
                    v_a_4274_ = crate::leanh::lean_ctor_get(v___x_4273_, 0);
                    v_isSharedCheck_4293_ = (!crate::leanh::lean_is_exclusive(v___x_4273_)) as u8;
                    if v_isSharedCheck_4293_ == 0 {
                        v___x_4276_ = v___x_4273_;
                        v_isShared_4277_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4274_);
                        crate::leanh::lean_dec(v___x_4273_);
                        v___x_4276_ = crate::leanh::lean_box(0);
                        v_isShared_4277_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4294_ = crate::leanh::lean_ctor_get(v___x_4273_, 0);
                    v_isSharedCheck_4301_ = (!crate::leanh::lean_is_exclusive(v___x_4273_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4296_ = v___x_4273_;
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4294_);
                        crate::leanh::lean_dec(v___x_4273_);
                        v___x_4296_ = crate::leanh::lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4278_ = crate::leanh::lean_ctor_get(v_a_4274_, 0);
                v_snd_4279_ = crate::leanh::lean_ctor_get(v_a_4274_, 1);
                v_isSharedCheck_4292_ = (!crate::leanh::lean_is_exclusive(v_a_4274_)) as u8;
                if v_isSharedCheck_4292_ == 0 {
                    v___x_4281_ = v_a_4274_;
                    v_isShared_4282_ = v_isSharedCheck_4292_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4279_);
                    crate::leanh::lean_inc(v_fst_4278_);
                    crate::leanh::lean_dec(v_a_4274_);
                    v___x_4281_ = crate::leanh::lean_box(0);
                    v_isShared_4282_ = v_isSharedCheck_4292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4283_ = crate::leanh::lean_box(0);
                v___x_4284_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4285_ = lean_array_get(v___x_4283_, v_fst_4278_, v___x_4284_);
                crate::leanh::lean_dec(v_fst_4278_);
                if v_isShared_4282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4281_, 0, v___x_4285_);
                    v___x_4287_ = v___x_4281_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4291_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_snd_4279_);
                    v___x_4287_ = v_reuseFailAlloc_4291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4277_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4276_, 0, v___x_4287_);
                    v___x_4289_ = v___x_4276_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
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
                    v_reuseFailAlloc_4300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
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
    mut v_mvarId_4302_: *mut crate::leanh::LeanObject,
    mut v_name_4303_: *mut crate::leanh::LeanObject,
    mut v_a_4304_: *mut crate::leanh::LeanObject,
    mut v_a_4305_: *mut crate::leanh::LeanObject,
    mut v_a_4306_: *mut crate::leanh::LeanObject,
    mut v_a_4307_: *mut crate::leanh::LeanObject,
    mut v_a_4308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4309_ = l_Lean_MVarId_intro(
        v_mvarId_4302_,
        v_name_4303_,
        v_a_4304_,
        v_a_4305_,
        v_a_4306_,
        v_a_4307_,
    );
    crate::leanh::lean_dec(v_a_4307_);
    crate::leanh::lean_dec_ref(v_a_4306_);
    crate::leanh::lean_dec(v_a_4305_);
    crate::leanh::lean_dec_ref(v_a_4304_);
    return v_res_4309_;
}
pub unsafe fn l_Lean_Meta_intro1Core(
    mut v_mvarId_4310_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_4311_: u8,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v_fst_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4339_: u8 = 0;
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v_a_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4317_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4318_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_4320_) == 0 {
                    v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                    v_isSharedCheck_4340_ = (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v___x_4323_ = v___x_4320_;
                        v_isShared_4324_ = v_isSharedCheck_4340_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4321_);
                        crate::leanh::lean_dec(v___x_4320_);
                        v___x_4323_ = crate::leanh::lean_box(0);
                        v_isShared_4324_ = v_isSharedCheck_4340_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4341_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                    v_isSharedCheck_4348_ = (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                    if v_isSharedCheck_4348_ == 0 {
                        v___x_4343_ = v___x_4320_;
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4341_);
                        crate::leanh::lean_dec(v___x_4320_);
                        v___x_4343_ = crate::leanh::lean_box(0);
                        v_isShared_4344_ = v_isSharedCheck_4348_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4325_ = crate::leanh::lean_ctor_get(v_a_4321_, 0);
                v_snd_4326_ = crate::leanh::lean_ctor_get(v_a_4321_, 1);
                v_isSharedCheck_4339_ = (!crate::leanh::lean_is_exclusive(v_a_4321_)) as u8;
                if v_isSharedCheck_4339_ == 0 {
                    v___x_4328_ = v_a_4321_;
                    v_isShared_4329_ = v_isSharedCheck_4339_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4326_);
                    crate::leanh::lean_inc(v_fst_4325_);
                    crate::leanh::lean_dec(v_a_4321_);
                    v___x_4328_ = crate::leanh::lean_box(0);
                    v_isShared_4329_ = v_isSharedCheck_4339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4330_ = crate::leanh::lean_box(0);
                v___x_4331_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4332_ = lean_array_get(v___x_4330_, v_fst_4325_, v___x_4331_);
                crate::leanh::lean_dec(v_fst_4325_);
                if v_isShared_4329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4328_, 0, v___x_4332_);
                    v___x_4334_ = v___x_4328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_snd_4326_);
                    v___x_4334_ = v_reuseFailAlloc_4338_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4334_);
                    v___x_4336_ = v___x_4323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
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
                    v_reuseFailAlloc_4347_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
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
    mut v_mvarId_4349_: *mut crate::leanh::LeanObject,
    mut v_preserveBinderNames_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
    mut v_a_4355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_preserveBinderNames_boxed_4356_: u8 = 0;
    let mut v_res_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_preserveBinderNames_boxed_4356_ =
        (crate::leanh::lean_unbox(v_preserveBinderNames_4350_) as u8);
    v_res_4357_ = l_Lean_Meta_intro1Core(
        v_mvarId_4349_,
        v_preserveBinderNames_boxed_4356_,
        v_a_4351_,
        v_a_4352_,
        v_a_4353_,
        v_a_4354_,
    );
    crate::leanh::lean_dec(v_a_4354_);
    crate::leanh::lean_dec_ref(v_a_4353_);
    crate::leanh::lean_dec(v_a_4352_);
    crate::leanh::lean_dec_ref(v_a_4351_);
    return v_res_4357_;
}
pub unsafe fn l_Lean_MVarId_intro1(
    mut v_mvarId_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_4366_: *mut crate::leanh::LeanObject,
    mut v_a_4367_: *mut crate::leanh::LeanObject,
    mut v_a_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4372_ = l_Lean_MVarId_intro1(v_mvarId_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
    crate::leanh::lean_dec(v_a_4370_);
    crate::leanh::lean_dec_ref(v_a_4369_);
    crate::leanh::lean_dec(v_a_4368_);
    crate::leanh::lean_dec_ref(v_a_4367_);
    return v_res_4372_;
}
pub unsafe fn l_Lean_MVarId_intro1P(
    mut v_mvarId_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_4381_: *mut crate::leanh::LeanObject,
    mut v_a_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Lean_MVarId_intro1P(v_mvarId_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
    crate::leanh::lean_dec(v_a_4385_);
    crate::leanh::lean_dec_ref(v_a_4384_);
    crate::leanh::lean_dec(v_a_4383_);
    crate::leanh::lean_dec_ref(v_a_4382_);
    return v_res_4387_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(
    mut v_msgData_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ = lean_st_ref_get(v___y_4392_);
    v_env_4395_ = crate::leanh::lean_ctor_get(v___x_4394_, 0);
    crate::leanh::lean_inc_ref(v_env_4395_);
    crate::leanh::lean_dec(v___x_4394_);
    v___x_4396_ = lean_st_ref_get(v___y_4390_);
    v_mctx_4397_ = crate::leanh::lean_ctor_get(v___x_4396_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4397_);
    crate::leanh::lean_dec(v___x_4396_);
    v_lctx_4398_ = crate::leanh::lean_ctor_get(v___y_4389_, 2);
    v_options_4399_ = crate::leanh::lean_ctor_get(v___y_4391_, 2);
    crate::leanh::lean_inc_ref(v_options_4399_);
    crate::leanh::lean_inc_ref(v_lctx_4398_);
    v___x_4400_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4400_, 0, v_env_4395_);
    crate::leanh::lean_ctor_set(v___x_4400_, 1, v_mctx_4397_);
    crate::leanh::lean_ctor_set(v___x_4400_, 2, v_lctx_4398_);
    crate::leanh::lean_ctor_set(v___x_4400_, 3, v_options_4399_);
    v___x_4401_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4401_, 0, v___x_4400_);
    crate::leanh::lean_ctor_set(v___x_4401_, 1, v_msgData_4388_);
    v___x_4402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4401_);
    return v___x_4402_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0___boxed(
    mut v_msgData_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msgData_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
    crate::leanh::lean_dec(v___y_4407_);
    crate::leanh::lean_dec_ref(v___y_4406_);
    crate::leanh::lean_dec(v___y_4405_);
    crate::leanh::lean_dec_ref(v___y_4404_);
    return v_res_4409_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
    mut v_msg_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
    mut v___y_4412_: *mut crate::leanh::LeanObject,
    mut v___y_4413_: *mut crate::leanh::LeanObject,
    mut v___y_4414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4416_ = crate::leanh::lean_ctor_get(v___y_4413_, 5);
                v___x_4417_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_intro1___00spec__0_spec__0(v_msg_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
                v_a_4418_ = crate::leanh::lean_ctor_get(v___x_4417_, 0);
                v_isSharedCheck_4426_ = (!crate::leanh::lean_is_exclusive(v___x_4417_)) as u8;
                if v_isSharedCheck_4426_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    v_isShared_4421_ = v_isSharedCheck_4426_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4418_);
                    crate::leanh::lean_dec(v___x_4417_);
                    v___x_4420_ = crate::leanh::lean_box(0);
                    v_isShared_4421_ = v_isSharedCheck_4426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4416_);
                v___x_4422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4422_, 0, v_ref_4416_);
                crate::leanh::lean_ctor_set(v___x_4422_, 1, v_a_4418_);
                if v_isShared_4421_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4420_, 1);
                    crate::leanh::lean_ctor_set(v___x_4420_, 0, v___x_4422_);
                    v___x_4424_ = v___x_4420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4422_);
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
    mut v_msg_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4433_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
        v_msg_4427_,
        v___y_4428_,
        v___y_4429_,
        v___y_4430_,
        v___y_4431_,
    );
    crate::leanh::lean_dec(v___y_4431_);
    crate::leanh::lean_dec_ref(v___y_4430_);
    crate::leanh::lean_dec(v___y_4429_);
    crate::leanh::lean_dec_ref(v___y_4428_);
    return v_res_4433_;
}
pub unsafe fn _init_l_Lean_MVarId_intro1___00__lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = l_Lean_MVarId_intro1___00__lam__0___closed__0;
    v___x_4436_ = l_Lean_stringToMessageData(v___x_4435_);
    return v___x_4436_;
}
pub unsafe fn l_Lean_MVarId_intro1___00__lam__0(
    mut v_mvarId_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4448_: u8 = 0;
    let mut v___y_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_unused_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_a_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v___x_4485_: u8 = 0;
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4493_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4497_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4437_);
                v___x_4443_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_4437_,
                    v___y_4438_,
                    v___y_4439_,
                    v___y_4440_,
                    v___y_4441_,
                );
                if crate::leanh::lean_obj_tag(v___x_4443_) == 0 {
                    v_a_4444_ = crate::leanh::lean_ctor_get(v___x_4443_, 0);
                    crate::leanh::lean_inc(v_a_4444_);
                    crate::leanh::lean_dec_ref_known(v___x_4443_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4444_) == 7 {
                        v_binderName_4445_ = crate::leanh::lean_ctor_get(v_a_4444_, 0);
                        crate::leanh::lean_inc(v_binderName_4445_);
                        v_binderType_4446_ = crate::leanh::lean_ctor_get(v_a_4444_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_4446_);
                        v_body_4447_ = crate::leanh::lean_ctor_get(v_a_4444_, 2);
                        crate::leanh::lean_inc_ref(v_body_4447_);
                        v_binderInfo_4448_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4444_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_a_4444_, 3);
                        v___x_4485_ = l_Lean_Expr_hasLooseBVars(v_body_4447_);
                        if v___x_4485_ == 0 {
                            v___y_4450_ = v___y_4438_;
                            v___y_4451_ = v___y_4439_;
                            v___y_4452_ = v___y_4440_;
                            v___y_4453_ = v___y_4441_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_body_4447_);
                            crate::leanh::lean_dec_ref(v_binderType_4446_);
                            crate::leanh::lean_dec(v_binderName_4445_);
                            v___x_4486_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_intro1___00__lam__0___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_intro1___00__lam__0___closed__1_once
                                ),
                                _init_l_Lean_MVarId_intro1___00__lam__0___closed__1,
                            );
                            v___x_4487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4487_, 0, v_mvarId_4437_);
                            v___x_4488_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4488_, 0, v___x_4486_);
                            crate::leanh::lean_ctor_set(v___x_4488_, 1, v___x_4487_);
                            v___x_4489_ =
                                l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0___redArg(
                                    v___x_4488_,
                                    v___y_4438_,
                                    v___y_4439_,
                                    v___y_4440_,
                                    v___y_4441_,
                                );
                            v_a_4490_ = crate::leanh::lean_ctor_get(v___x_4489_, 0);
                            v_isSharedCheck_4497_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4489_)) as u8;
                            if v_isSharedCheck_4497_ == 0 {
                                v___x_4492_ = v___x_4489_;
                                v_isShared_4493_ = v_isSharedCheck_4497_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4490_);
                                crate::leanh::lean_dec(v___x_4489_);
                                v___x_4492_ = crate::leanh::lean_box(0);
                                v_isShared_4493_ = v_isSharedCheck_4497_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4444_);
                        v___x_4498_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_intro1___00__lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_intro1___00__lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_intro1___00__lam__0___closed__1,
                        );
                        v___x_4499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4499_, 0, v_mvarId_4437_);
                        v___x_4500_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4500_, 0, v___x_4498_);
                        crate::leanh::lean_ctor_set(v___x_4500_, 1, v___x_4499_);
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
                    crate::leanh::lean_dec(v_mvarId_4437_);
                    v_a_4502_ = crate::leanh::lean_ctor_get(v___x_4443_, 0);
                    v_isSharedCheck_4509_ = (!crate::leanh::lean_is_exclusive(v___x_4443_)) as u8;
                    if v_isSharedCheck_4509_ == 0 {
                        v___x_4504_ = v___x_4443_;
                        v_isShared_4505_ = v_isSharedCheck_4509_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4502_);
                        crate::leanh::lean_dec(v___x_4443_);
                        v___x_4504_ = crate::leanh::lean_box(0);
                        v_isShared_4505_ = v_isSharedCheck_4509_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_mvarId_4437_);
                v___x_4454_ = l_Lean_MVarId_getTag(
                    v_mvarId_4437_,
                    v___y_4450_,
                    v___y_4451_,
                    v___y_4452_,
                    v___y_4453_,
                );
                if crate::leanh::lean_obj_tag(v___x_4454_) == 0 {
                    v_a_4455_ = crate::leanh::lean_ctor_get(v___x_4454_, 0);
                    crate::leanh::lean_inc(v_a_4455_);
                    crate::leanh::lean_dec_ref_known(v___x_4454_, 1);
                    v___x_4456_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_body_4447_,
                        v_a_4455_,
                        v___y_4450_,
                        v___y_4451_,
                        v___y_4452_,
                        v___y_4453_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4456_) == 0 {
                        v_a_4457_ = crate::leanh::lean_ctor_get(v___x_4456_, 0);
                        crate::leanh::lean_inc_n(v_a_4457_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4456_, 1);
                        v___x_4458_ = l_Lean_Expr_lam___override(
                            v_binderName_4445_,
                            v_binderType_4446_,
                            v_a_4457_,
                            v_binderInfo_4448_,
                        );
                        v___x_4459_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__0___redArg(v_mvarId_4437_, v___x_4458_, v___y_4451_);
                        v_isSharedCheck_4467_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4467_ == 0 {
                            v_unused_4468_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                            crate::leanh::lean_dec(v_unused_4468_);
                            v___x_4461_ = v___x_4459_;
                            v_isShared_4462_ = v_isSharedCheck_4467_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4459_);
                            v___x_4461_ = crate::leanh::lean_box(0);
                            v_isShared_4462_ = v_isSharedCheck_4467_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_binderType_4446_);
                        crate::leanh::lean_dec(v_binderName_4445_);
                        crate::leanh::lean_dec(v_mvarId_4437_);
                        v_a_4469_ = crate::leanh::lean_ctor_get(v___x_4456_, 0);
                        v_isSharedCheck_4476_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4456_)) as u8;
                        if v_isSharedCheck_4476_ == 0 {
                            v___x_4471_ = v___x_4456_;
                            v_isShared_4472_ = v_isSharedCheck_4476_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4469_);
                            crate::leanh::lean_dec(v___x_4456_);
                            v___x_4471_ = crate::leanh::lean_box(0);
                            v_isShared_4472_ = v_isSharedCheck_4476_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_4447_);
                    crate::leanh::lean_dec_ref(v_binderType_4446_);
                    crate::leanh::lean_dec(v_binderName_4445_);
                    crate::leanh::lean_dec(v_mvarId_4437_);
                    v_a_4477_ = crate::leanh::lean_ctor_get(v___x_4454_, 0);
                    v_isSharedCheck_4484_ = (!crate::leanh::lean_is_exclusive(v___x_4454_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4479_ = v___x_4454_;
                        v_isShared_4480_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4477_);
                        crate::leanh::lean_dec(v___x_4454_);
                        v___x_4479_ = crate::leanh::lean_box(0);
                        v_isShared_4480_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4463_ = l_Lean_Expr_mvarId_x21(v_a_4457_);
                crate::leanh::lean_dec(v_a_4457_);
                if v_isShared_4462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4461_, 0, v___x_4463_);
                    v___x_4465_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
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
                    v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
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
                    v_reuseFailAlloc_4483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
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
                    v_reuseFailAlloc_4496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
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
                    v_reuseFailAlloc_4508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
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
    mut v_mvarId_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_MVarId_intro1___00__lam__0(
        v_mvarId_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
    );
    crate::leanh::lean_dec(v___y_4514_);
    crate::leanh::lean_dec_ref(v___y_4513_);
    crate::leanh::lean_dec(v___y_4512_);
    crate::leanh::lean_dec_ref(v___y_4511_);
    return v_res_4516_;
}
pub unsafe fn l_Lean_MVarId_intro1__(
    mut v_mvarId_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
    mut v_a_4519_: *mut crate::leanh::LeanObject,
    mut v_a_4520_: *mut crate::leanh::LeanObject,
    mut v_a_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_4517_);
    v___f_4523_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_intro1___00__lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4523_, 0, v_mvarId_4517_);
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
    mut v_mvarId_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ =
        l_Lean_MVarId_intro1__(v_mvarId_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
    crate::leanh::lean_dec(v_a_4529_);
    crate::leanh::lean_dec_ref(v_a_4528_);
    crate::leanh::lean_dec(v_a_4527_);
    crate::leanh::lean_dec_ref(v_a_4526_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(
    mut v_00_u03b1_4532_: *mut crate::leanh::LeanObject,
    mut v_msg_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4540_: *mut crate::leanh::LeanObject,
    mut v_msg_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4547_ = l_Lean_throwError___at___00Lean_MVarId_intro1___00spec__0(
        v_00_u03b1_4540_,
        v_msg_4541_,
        v___y_4542_,
        v___y_4543_,
        v___y_4544_,
        v___y_4545_,
    );
    crate::leanh::lean_dec(v___y_4545_);
    crate::leanh::lean_dec_ref(v___y_4544_);
    crate::leanh::lean_dec(v___y_4543_);
    crate::leanh::lean_dec_ref(v___y_4542_);
    return v_res_4547_;
}
pub unsafe fn l_Lean_Meta_getIntrosSize(
    mut v_x_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4548_) {
                7 => {
                    v_body_4549_ = crate::leanh::lean_ctor_get(v_x_4548_, 2);
                    v___x_4550_ = l_Lean_Meta_getIntrosSize(v_body_4549_);
                    v___x_4551_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4552_ = lean_nat_add(v___x_4550_, v___x_4551_);
                    crate::leanh::lean_dec(v___x_4550_);
                    return v___x_4552_;
                }
                8 => {
                    v_body_4553_ = crate::leanh::lean_ctor_get(v_x_4548_, 3);
                    v___x_4554_ = l_Lean_Meta_getIntrosSize(v_body_4553_);
                    v___x_4555_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4556_ = lean_nat_add(v___x_4554_, v___x_4555_);
                    crate::leanh::lean_dec(v___x_4554_);
                    return v___x_4556_;
                }
                10 => {
                    v_expr_4557_ = crate::leanh::lean_ctor_get(v_x_4548_, 1);
                    v_x_4548_ = v_expr_4557_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_4559_ = crate::leanh::lean_unsigned_to_nat(0);
                    return v___x_4559_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getIntrosSize___boxed(
    mut v_x_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Lean_Meta_getIntrosSize(v_x_4560_);
    crate::leanh::lean_dec_ref(v_x_4560_);
    return v_res_4561_;
}
pub unsafe fn l_Lean_MVarId_intros(
    mut v_mvarId_4562_: *mut crate::leanh::LeanObject,
    mut v_a_4563_: *mut crate::leanh::LeanObject,
    mut v_a_4564_: *mut crate::leanh::LeanObject,
    mut v_a_4565_: *mut crate::leanh::LeanObject,
    mut v_a_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_a_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4589_: u8 = 0;
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4562_);
                v___x_4568_ = l_Lean_MVarId_getType(
                    v_mvarId_4562_,
                    v_a_4563_,
                    v_a_4564_,
                    v_a_4565_,
                    v_a_4566_,
                );
                if crate::leanh::lean_obj_tag(v___x_4568_) == 0 {
                    v_a_4569_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                    crate::leanh::lean_inc(v_a_4569_);
                    crate::leanh::lean_dec_ref_known(v___x_4568_, 1);
                    v___x_4570_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___at___00Lean_Meta_introNCore_spec__0_spec__4___redArg(v_a_4569_, v_a_4564_);
                    v_a_4571_ = crate::leanh::lean_ctor_get(v___x_4570_, 0);
                    v_isSharedCheck_4585_ = (!crate::leanh::lean_is_exclusive(v___x_4570_)) as u8;
                    if v_isSharedCheck_4585_ == 0 {
                        v___x_4573_ = v___x_4570_;
                        v_isShared_4574_ = v_isSharedCheck_4585_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4571_);
                        crate::leanh::lean_dec(v___x_4570_);
                        v___x_4573_ = crate::leanh::lean_box(0);
                        v_isShared_4574_ = v_isSharedCheck_4585_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4562_);
                    v_a_4586_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                    v_isSharedCheck_4593_ = (!crate::leanh::lean_is_exclusive(v___x_4568_)) as u8;
                    if v_isSharedCheck_4593_ == 0 {
                        v___x_4588_ = v___x_4568_;
                        v_isShared_4589_ = v_isSharedCheck_4593_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4586_);
                        crate::leanh::lean_dec(v___x_4568_);
                        v___x_4588_ = crate::leanh::lean_box(0);
                        v_isShared_4589_ = v_isSharedCheck_4593_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4575_ = l_Lean_Meta_getIntrosSize(v_a_4571_);
                crate::leanh::lean_dec(v_a_4571_);
                v___x_4576_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4577_ = lean_nat_dec_eq(v___x_4575_, v___x_4576_);
                if v___x_4577_ == 0 {
                    crate::leanh::lean_del_object(v___x_4573_);
                    v___x_4578_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v___x_4575_);
                    v___x_4580_ = l_Lean_Meta_introNCore___closed__0;
                    v___x_4581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4581_, 0, v___x_4580_);
                    crate::leanh::lean_ctor_set(v___x_4581_, 1, v_mvarId_4562_);
                    if v_isShared_4574_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4573_, 0, v___x_4581_);
                        v___x_4583_ = v___x_4573_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4581_);
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
                    v_reuseFailAlloc_4592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
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
    mut v_mvarId_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
    mut v_a_4598_: *mut crate::leanh::LeanObject,
    mut v_a_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4600_ = l_Lean_MVarId_intros(v_mvarId_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
    crate::leanh::lean_dec(v_a_4598_);
    crate::leanh::lean_dec_ref(v_a_4597_);
    crate::leanh::lean_dec(v_a_4596_);
    crate::leanh::lean_dec_ref(v_a_4595_);
    return v_res_4600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Intro(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Intro_3089346791____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_tactic_hygienic = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_tactic_hygienic);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Intro(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Intro(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Intro(builtin);
}
