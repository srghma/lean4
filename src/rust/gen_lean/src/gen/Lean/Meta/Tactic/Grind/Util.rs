// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Util
// Imports: Lean.Meta.Tactic.Simp.Simproc Init.Simproc Lean.Meta.Tactic.Clear Lean.Meta.Sym.Util Init.Grind.Config Init.Grind.Util Lean.Structure
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_find_expr, lean_grind_normalize, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed,
    lean_ptr_addr, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Grind::Config::{
    initialize_Init_Grind_Config, runtime_initialize_Init_Grind_Config,
};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_maxRecDepthErrorMessage, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Init::System::CancelToken::l_IO_CancelToken_isSet;
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_Exception_isRuntime, l_Lean_mkArrow,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_interruptExceptionId};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_forallE___override, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasExprMVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_isFalse,
    l_Lean_Expr_isMData___boxed, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_mvarId_x21, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_ExprStructEq_beq, l_Lean_ExprStructEq_hash,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNot,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkAuxDecl, l_Lean_LocalContext_mkLetDecl, l_Lean_LocalContext_mkLocalDecl,
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_isImplementationDetail,
    l_Lean_LocalDecl_userName, l_Lean_instInhabitedLocalContext_default,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AbstractMVars::l_Lean_Meta_abstractMVars;
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkExpectedPropHint,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_MVarId_getDecl, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVarAt,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_foldProjs,
    l_Lean_Meta_Sym_unfoldReducible___boxed, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::{
    initialize_Lean_Meta_Tactic_Clear, l_Lean_MVarId_clear,
    runtime_initialize_Lean_Meta_Tactic_Clear,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_Simprocs_add,
    l_Lean_Meta_Simp_registerBuiltinDSimproc, runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::Meta::Transform::l_Lean_Core_betaReduce;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Structure::{initialize_Lean_Structure, runtime_initialize_Lean_Structure};
pub static l_Lean_MVarId_ensureNoMVar___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_ensureNoMVar___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
                as *mut leanh::LeanObject,
            15947788021050471391 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_ensureNoMVar___closed__2_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            103, 111, 97, 108, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 109, 101, 116, 97,
            118, 97, 114, 105, 97, 98, 108, 101, 115, 0,
        ],
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_ensureNoMVar___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_ensureNoMVar___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_ensureNoMVar___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 118, 97, 114, 67, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 76, 67, 116, 120, 77, 86, 97, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2_value: leanh::LeanStringObject<55> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 110, 32, 97, 115, 115, 111, 99, 105, 97, 116, 101, 100, 32, 102, 117, 108, 108, 32, 110, 97, 109, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_unfoldReducible___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Sym_unfoldReducible___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_unfoldReducible___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_unfoldReducible___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_betaReduce___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_betaReduce___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_betaReduce___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_betaReduce___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            907667957179513571 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0],
};
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        98, 121, 67, 111, 110, 116, 114, 97, 100, 105, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        10854111772627758120 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value)
                as *mut leanh::LeanObject,
            3628558105408452239 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_byContra_x3f___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [98, 121, 95, 99, 111, 110, 116, 114, 97, 0],
    };
static mut l_Lean_MVarId_byContra_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_byContra_x3f___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
                as *mut leanh::LeanObject,
            15947788021050471391 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_byContra_x3f___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            11419739819762551189 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byContra_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [116, 104, 101, 32, 103, 111, 97, 108, 32, 109, 101, 110, 116, 105, 111, 110, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2_value: leanh::LeanStringObject<94> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [96, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 98, 101, 105, 110, 103, 32, 100, 101, 102, 105, 110, 101, 100, 46, 32, 84, 111, 32, 97, 118, 111, 105, 100, 32, 99, 105, 114, 99, 117, 108, 97, 114, 32, 114, 101, 97, 115, 111, 110, 105, 110, 103, 44, 32, 116, 114, 121, 32, 114, 101, 119, 114, 105, 116, 105, 110, 103, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 116, 111, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 98, 101, 102, 111, 114, 101, 32, 117, 115, 105, 110, 103, 32, 96, 103, 114, 105, 110, 100, 96, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_clearImplDetails___closed__0_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            99, 108, 101, 97, 114, 95, 97, 117, 120, 95, 100, 101, 99, 108, 115, 0,
        ],
    };
static mut l_Lean_MVarId_clearImplDetails___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_MVarId_clearImplDetails___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
                as *mut leanh::LeanObject,
            15947788021050471391 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_clearImplDetails___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__0_value)
                as *mut leanh::LeanObject,
            12811869134523501583 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_clearImplDetails___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0_value:
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
    m_fun: l_Lean_Expr_isMData___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__1_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__2_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [77, 97, 116, 99, 104, 67, 111, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__2_value)
                as *mut leanh::LeanObject,
            16774854854508800365 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [80, 114, 101, 77, 97, 116, 99, 104, 67, 111, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value)
                as *mut leanh::LeanObject,
            2148952242689989847 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [114, 101, 100, 117, 99, 101, 80, 114, 101, 77, 97, 116, 99, 104, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value) as *mut leanh::LeanObject,15218882539576375456 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject,8386783702137954454 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: leanh::LeanArrayObject<2> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_replacePreMatchCond___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_isPreMatchCond___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_replacePreMatchCond___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_replacePreMatchCond___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_replacePreMatchCond___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_replacePreMatchCond___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_replacePreMatchCond___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_replacePreMatchCond___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_replacePreMatchCond___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_replacePreMatchCond___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_isIte___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 116, 101, 0],
    };
static mut l_Lean_Meta_Grind_isIte___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isIte___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_isIte___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isIte___closed__0_value)
                as *mut leanh::LeanObject,
            18356704233129443855 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isIte___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isIte___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_isDIte___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [100, 105, 116, 101, 0],
    };
static mut l_Lean_Meta_Grind_isDIte___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isDIte___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_isDIte___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isDIte___closed__0_value)
                as *mut leanh::LeanObject,
            8391571994004792969 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isDIte___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isDIte___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
    mut v_e_3665_: *mut leanh::LeanObject,
    mut v___y_3666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3688_: u8 = 0;
    let mut v_unused_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3668_ = l_Lean_Expr_hasMVar(v_e_3665_);
                if v___x_3668_ == 0 {
                    v___x_3669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3669_, 0, v_e_3665_);
                    return v___x_3669_;
                } else {
                    v___x_3670_ = lean_st_ref_get(v___y_3666_);
                    v_mctx_3671_ = leanh::lean_ctor_get(v___x_3670_, 0);
                    leanh::lean_inc_ref(v_mctx_3671_);
                    leanh::lean_dec(v___x_3670_);
                    v___x_3672_ = l_Lean_instantiateMVarsCore(v_mctx_3671_, v_e_3665_);
                    v_fst_3673_ = leanh::lean_ctor_get(v___x_3672_, 0);
                    leanh::lean_inc(v_fst_3673_);
                    v_snd_3674_ = leanh::lean_ctor_get(v___x_3672_, 1);
                    leanh::lean_inc(v_snd_3674_);
                    leanh::lean_dec_ref(v___x_3672_);
                    v___x_3675_ = lean_st_ref_take(v___y_3666_);
                    v_cache_3676_ = leanh::lean_ctor_get(v___x_3675_, 1);
                    v_zetaDeltaFVarIds_3677_ = leanh::lean_ctor_get(v___x_3675_, 2);
                    v_postponed_3678_ = leanh::lean_ctor_get(v___x_3675_, 3);
                    v_diag_3679_ = leanh::lean_ctor_get(v___x_3675_, 4);
                    v_isSharedCheck_3688_ = (!leanh::lean_is_exclusive(v___x_3675_)) as u8;
                    if v_isSharedCheck_3688_ == 0 {
                        v_unused_3689_ = leanh::lean_ctor_get(v___x_3675_, 0);
                        leanh::lean_dec(v_unused_3689_);
                        v___x_3681_ = v___x_3675_;
                        v_isShared_3682_ = v_isSharedCheck_3688_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3679_);
                        leanh::lean_inc(v_postponed_3678_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3677_);
                        leanh::lean_inc(v_cache_3676_);
                        leanh::lean_dec(v___x_3675_);
                        v___x_3681_ = leanh::lean_box(0);
                        v_isShared_3682_ = v_isSharedCheck_3688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3682_ == 0 {
                    leanh::lean_ctor_set(v___x_3681_, 0, v_snd_3674_);
                    v___x_3684_ = v___x_3681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_snd_3674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_cache_3676_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3687_,
                        2,
                        v_zetaDeltaFVarIds_3677_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_postponed_3678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_diag_3679_);
                    v___x_3684_ = v_reuseFailAlloc_3687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3685_ = lean_st_ref_set(v___y_3666_, v___x_3684_);
                v___x_3686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3686_, 0, v_fst_3673_);
                return v___x_3686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg___boxed(
    mut v_e_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
        v_e_3690_,
        v___y_3691_,
    );
    leanh::lean_dec(v___y_3691_);
    return v_res_3693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(
    mut v_e_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
    mut v___y_3696_: *mut leanh::LeanObject,
    mut v___y_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
        v_e_3694_,
        v___y_3696_,
    );
    return v___x_3700_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___boxed(
    mut v_e_3701_: *mut leanh::LeanObject,
    mut v___y_3702_: *mut leanh::LeanObject,
    mut v___y_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(
        v_e_3701_,
        v___y_3702_,
        v___y_3703_,
        v___y_3704_,
        v___y_3705_,
    );
    leanh::lean_dec(v___y_3705_);
    leanh::lean_dec_ref(v___y_3704_);
    leanh::lean_dec(v___y_3703_);
    leanh::lean_dec_ref(v___y_3702_);
    return v_res_3707_;
}
pub unsafe fn _init_l_Lean_MVarId_ensureNoMVar___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l_Lean_MVarId_ensureNoMVar___closed__3;
    v___x_3715_ = l_Lean_MessageData_ofFormat(v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_MVarId_ensureNoMVar___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_ensureNoMVar___closed__4),
        core::ptr::addr_of_mut!(l_Lean_MVarId_ensureNoMVar___closed__4_once),
        _init_l_Lean_MVarId_ensureNoMVar___closed__4,
    );
    v___x_3717_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3717_, 0, v___x_3716_);
    return v___x_3717_;
}
pub unsafe fn l_Lean_MVarId_ensureNoMVar(
    mut v_mvarId_3718_: *mut leanh::LeanObject,
    mut v_a_3719_: *mut leanh::LeanObject,
    mut v_a_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut v_a_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3718_);
                v___x_3724_ = l_Lean_MVarId_getType(
                    v_mvarId_3718_,
                    v_a_3719_,
                    v_a_3720_,
                    v_a_3721_,
                    v_a_3722_,
                );
                if leanh::lean_obj_tag(v___x_3724_) == 0 {
                    v_a_3725_ = leanh::lean_ctor_get(v___x_3724_, 0);
                    leanh::lean_inc(v_a_3725_);
                    leanh::lean_dec_ref_known(v___x_3724_, 1);
                    v___x_3726_ =
                        l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
                            v_a_3725_, v_a_3720_,
                        );
                    v_a_3727_ = leanh::lean_ctor_get(v___x_3726_, 0);
                    v_isSharedCheck_3739_ = (!leanh::lean_is_exclusive(v___x_3726_)) as u8;
                    if v_isSharedCheck_3739_ == 0 {
                        v___x_3729_ = v___x_3726_;
                        v_isShared_3730_ = v_isSharedCheck_3739_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3727_);
                        leanh::lean_dec(v___x_3726_);
                        v___x_3729_ = leanh::lean_box(0);
                        v_isShared_3730_ = v_isSharedCheck_3739_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_3718_);
                    v_a_3740_ = leanh::lean_ctor_get(v___x_3724_, 0);
                    v_isSharedCheck_3747_ = (!leanh::lean_is_exclusive(v___x_3724_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3724_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3740_);
                        leanh::lean_dec(v___x_3724_);
                        v___x_3742_ = leanh::lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3731_ = l_Lean_Expr_hasExprMVar(v_a_3727_);
                leanh::lean_dec(v_a_3727_);
                if v___x_3731_ == 0 {
                    leanh::lean_dec(v_mvarId_3718_);
                    v___x_3732_ = leanh::lean_box(0);
                    if v_isShared_3730_ == 0 {
                        leanh::lean_ctor_set(v___x_3729_, 0, v___x_3732_);
                        v___x_3734_ = v___x_3729_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
                        v___x_3734_ = v_reuseFailAlloc_3735_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3729_);
                    v___x_3736_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                    v___x_3737_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_ensureNoMVar___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_ensureNoMVar___closed__5_once),
                        _init_l_Lean_MVarId_ensureNoMVar___closed__5,
                    );
                    v___x_3738_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_3736_,
                        v_mvarId_3718_,
                        v___x_3737_,
                        v_a_3719_,
                        v_a_3720_,
                        v_a_3721_,
                        v_a_3722_,
                    );
                    return v___x_3738_;
                }
            }
            2 => {
                return v___x_3734_;
            }
            3 => {
                if v_isShared_3743_ == 0 {
                    v___x_3745_ = v___x_3742_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
                    v___x_3745_ = v_reuseFailAlloc_3746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_ensureNoMVar___boxed(
    mut v_mvarId_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_a_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ =
        l_Lean_MVarId_ensureNoMVar(v_mvarId_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
    leanh::lean_dec(v_a_3752_);
    leanh::lean_dec_ref(v_a_3751_);
    leanh::lean_dec(v_a_3750_);
    leanh::lean_dec_ref(v_a_3749_);
    return v_res_3754_;
}
pub unsafe fn _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_3755_;
}
pub unsafe fn l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(
    mut v_msg_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v_toFunctor_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___f_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v_toFunctor_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___f_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361__overap_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut v_unused_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut v_unused_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_unused_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0);
                v___x_3767_ = l_StateRefT_x27_instMonad___redArg(v___x_3766_);
                v_toApplicative_3768_ = leanh::lean_ctor_get(v___x_3767_, 0);
                v_isSharedCheck_3829_ = (!leanh::lean_is_exclusive(v___x_3767_)) as u8;
                if v_isSharedCheck_3829_ == 0 {
                    v_unused_3830_ = leanh::lean_ctor_get(v___x_3767_, 1);
                    leanh::lean_dec(v_unused_3830_);
                    v___x_3770_ = v___x_3767_;
                    v_isShared_3771_ = v_isSharedCheck_3829_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3768_);
                    leanh::lean_dec(v___x_3767_);
                    v___x_3770_ = leanh::lean_box(0);
                    v_isShared_3771_ = v_isSharedCheck_3829_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3772_ = leanh::lean_ctor_get(v_toApplicative_3768_, 0);
                v_toSeq_3773_ = leanh::lean_ctor_get(v_toApplicative_3768_, 2);
                v_toSeqLeft_3774_ = leanh::lean_ctor_get(v_toApplicative_3768_, 3);
                v_toSeqRight_3775_ = leanh::lean_ctor_get(v_toApplicative_3768_, 4);
                v_isSharedCheck_3827_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3768_)) as u8;
                if v_isSharedCheck_3827_ == 0 {
                    v_unused_3828_ = leanh::lean_ctor_get(v_toApplicative_3768_, 1);
                    leanh::lean_dec(v_unused_3828_);
                    v___x_3777_ = v_toApplicative_3768_;
                    v_isShared_3778_ = v_isSharedCheck_3827_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3775_);
                    leanh::lean_inc(v_toSeqLeft_3774_);
                    leanh::lean_inc(v_toSeq_3773_);
                    leanh::lean_inc(v_toFunctor_3772_);
                    leanh::lean_dec(v_toApplicative_3768_);
                    v___x_3777_ = leanh::lean_box(0);
                    v_isShared_3778_ = v_isSharedCheck_3827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3779_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1;
                v___f_3780_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2;
                leanh::lean_inc_ref(v_toFunctor_3772_);
                v___f_3781_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3781_, 0, v_toFunctor_3772_);
                v___f_3782_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3782_, 0, v_toFunctor_3772_);
                v___x_3783_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3783_, 0, v___f_3781_);
                leanh::lean_ctor_set(v___x_3783_, 1, v___f_3782_);
                v___f_3784_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3784_, 0, v_toSeqRight_3775_);
                v___f_3785_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3785_, 0, v_toSeqLeft_3774_);
                v___f_3786_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3786_, 0, v_toSeq_3773_);
                if v_isShared_3778_ == 0 {
                    leanh::lean_ctor_set(v___x_3777_, 4, v___f_3784_);
                    leanh::lean_ctor_set(v___x_3777_, 3, v___f_3785_);
                    leanh::lean_ctor_set(v___x_3777_, 2, v___f_3786_);
                    leanh::lean_ctor_set(v___x_3777_, 1, v___f_3779_);
                    leanh::lean_ctor_set(v___x_3777_, 0, v___x_3783_);
                    v___x_3788_ = v___x_3777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___f_3779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 2, v___f_3786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 3, v___f_3785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 4, v___f_3784_);
                    v___x_3788_ = v_reuseFailAlloc_3826_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3771_ == 0 {
                    leanh::lean_ctor_set(v___x_3770_, 1, v___f_3780_);
                    leanh::lean_ctor_set(v___x_3770_, 0, v___x_3788_);
                    v___x_3790_ = v___x_3770_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___f_3780_);
                    v___x_3790_ = v_reuseFailAlloc_3825_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3791_ = l_StateRefT_x27_instMonad___redArg(v___x_3790_);
                v_toApplicative_3792_ = leanh::lean_ctor_get(v___x_3791_, 0);
                v_isSharedCheck_3823_ = (!leanh::lean_is_exclusive(v___x_3791_)) as u8;
                if v_isSharedCheck_3823_ == 0 {
                    v_unused_3824_ = leanh::lean_ctor_get(v___x_3791_, 1);
                    leanh::lean_dec(v_unused_3824_);
                    v___x_3794_ = v___x_3791_;
                    v_isShared_3795_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3792_);
                    leanh::lean_dec(v___x_3791_);
                    v___x_3794_ = leanh::lean_box(0);
                    v_isShared_3795_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3796_ = leanh::lean_ctor_get(v_toApplicative_3792_, 0);
                v_toSeq_3797_ = leanh::lean_ctor_get(v_toApplicative_3792_, 2);
                v_toSeqLeft_3798_ = leanh::lean_ctor_get(v_toApplicative_3792_, 3);
                v_toSeqRight_3799_ = leanh::lean_ctor_get(v_toApplicative_3792_, 4);
                v_isSharedCheck_3821_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3792_)) as u8;
                if v_isSharedCheck_3821_ == 0 {
                    v_unused_3822_ = leanh::lean_ctor_get(v_toApplicative_3792_, 1);
                    leanh::lean_dec(v_unused_3822_);
                    v___x_3801_ = v_toApplicative_3792_;
                    v_isShared_3802_ = v_isSharedCheck_3821_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3799_);
                    leanh::lean_inc(v_toSeqLeft_3798_);
                    leanh::lean_inc(v_toSeq_3797_);
                    leanh::lean_inc(v_toFunctor_3796_);
                    leanh::lean_dec(v_toApplicative_3792_);
                    v___x_3801_ = leanh::lean_box(0);
                    v_isShared_3802_ = v_isSharedCheck_3821_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3803_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3;
                v___f_3804_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4;
                leanh::lean_inc_ref(v_toFunctor_3796_);
                v___f_3805_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3805_, 0, v_toFunctor_3796_);
                v___f_3806_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3806_, 0, v_toFunctor_3796_);
                v___x_3807_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3807_, 0, v___f_3805_);
                leanh::lean_ctor_set(v___x_3807_, 1, v___f_3806_);
                v___f_3808_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3808_, 0, v_toSeqRight_3799_);
                v___f_3809_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3809_, 0, v_toSeqLeft_3798_);
                v___f_3810_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3810_, 0, v_toSeq_3797_);
                if v_isShared_3802_ == 0 {
                    leanh::lean_ctor_set(v___x_3801_, 4, v___f_3808_);
                    leanh::lean_ctor_set(v___x_3801_, 3, v___f_3809_);
                    leanh::lean_ctor_set(v___x_3801_, 2, v___f_3810_);
                    leanh::lean_ctor_set(v___x_3801_, 1, v___f_3803_);
                    leanh::lean_ctor_set(v___x_3801_, 0, v___x_3807_);
                    v___x_3812_ = v___x_3801_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___f_3803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 2, v___f_3810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 3, v___f_3809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 4, v___f_3808_);
                    v___x_3812_ = v_reuseFailAlloc_3820_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3795_ == 0 {
                    leanh::lean_ctor_set(v___x_3794_, 1, v___f_3804_);
                    leanh::lean_ctor_set(v___x_3794_, 0, v___x_3812_);
                    v___x_3814_ = v___x_3794_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___f_3804_);
                    v___x_3814_ = v_reuseFailAlloc_3819_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3815_ = l_Lean_instInhabitedLocalContext_default;
                v___x_3816_ = l_instInhabitedOfMonad___redArg(v___x_3814_, v___x_3815_);
                v___x_1361__overap_3817_ = lean_panic_fn_borrowed(v___x_3816_, v_msg_3760_);
                leanh::lean_dec(v___x_3816_);
                leanh::lean_inc(v___y_3764_);
                leanh::lean_inc_ref(v___y_3763_);
                leanh::lean_inc(v___y_3762_);
                leanh::lean_inc_ref(v___y_3761_);
                v___x_3818_ = leanh::lean_apply_5(
                    v___x_1361__overap_3817_,
                    v___y_3761_,
                    v___y_3762_,
                    v___y_3763_,
                    v___y_3764_,
                    leanh::lean_box(0),
                );
                return v___x_3818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___boxed(
    mut v_msg_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3837_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v_msg_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
    leanh::lean_dec(v___y_3835_);
    leanh::lean_dec_ref(v___y_3834_);
    leanh::lean_dec(v___y_3833_);
    leanh::lean_dec_ref(v___y_3832_);
    return v_res_3837_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(
    mut v_t_3838_: *mut leanh::LeanObject,
    mut v_k_3839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3838_) == 0 {
                    v_k_3840_ = leanh::lean_ctor_get(v_t_3838_, 1);
                    v_v_3841_ = leanh::lean_ctor_get(v_t_3838_, 2);
                    v_l_3842_ = leanh::lean_ctor_get(v_t_3838_, 3);
                    v_r_3843_ = leanh::lean_ctor_get(v_t_3838_, 4);
                    v___x_3844_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3839_, v_k_3840_);
                    match v___x_3844_ {
                        0 => {
                            v_t_3838_ = v_l_3842_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_3841_);
                            v___x_3846_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3846_, 0, v_v_3841_);
                            return v___x_3846_;
                        }
                        _ => {
                            v_t_3838_ = v_r_3843_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_3848_ = leanh::lean_box(0);
                    return v___x_3848_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg___boxed(
    mut v_t_3849_: *mut leanh::LeanObject,
    mut v_k_3850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_3849_, v_k_3850_);
    leanh::lean_dec(v_k_3850_);
    leanh::lean_dec(v_t_3849_);
    return v_res_3851_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(
    mut v_auxDeclToFullName_3856_: *mut leanh::LeanObject,
    mut v_as_3857_: *mut leanh::LeanObject,
    mut v_i_3858_: usize,
    mut v_stop_3859_: usize,
    mut v_b_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
    mut v___y_3862_: *mut leanh::LeanObject,
    mut v___y_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: usize = 0;
    let mut v___x_3869_: usize = 0;
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3874_: u8 = 0;
    let mut v_fvarId_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_fvarId_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_3907_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_fvarId_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_3923_: u8 = 0;
    let mut v_kind_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_a_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3941_: u8 = 0;
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3871_ = lean_usize_dec_eq(v_i_3858_, v_stop_3859_);
                if v___x_3871_ == 0 {
                    v___x_3872_ = lean_array_uget_borrowed(v_as_3857_, v_i_3858_);
                    if leanh::lean_obj_tag(v___x_3872_) == 0 {
                        v_a_3867_ = v_b_3860_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3873_ = leanh::lean_ctor_get(v___x_3872_, 0);
                        if leanh::lean_obj_tag(v_val_3873_) == 0 {
                            v_kind_3874_ = leanh::lean_ctor_get_uint8(
                                v_val_3873_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1)
                                    as u32,
                            );
                            if v_kind_3874_ == 2 {
                                v_fvarId_3875_ = leanh::lean_ctor_get(v_val_3873_, 1);
                                v_userName_3876_ = leanh::lean_ctor_get(v_val_3873_, 2);
                                v_type_3877_ = leanh::lean_ctor_get(v_val_3873_, 3);
                                leanh::lean_inc_ref(v_type_3877_);
                                v___x_3878_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_3877_, v___y_3862_);
                                if leanh::lean_obj_tag(v___x_3878_) == 0 {
                                    v_a_3879_ = leanh::lean_ctor_get(v___x_3878_, 0);
                                    leanh::lean_inc(v_a_3879_);
                                    leanh::lean_dec_ref_known(v___x_3878_, 1);
                                    v___x_3880_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_auxDeclToFullName_3856_, v_fvarId_3875_);
                                    if leanh::lean_obj_tag(v___x_3880_) == 1 {
                                        v_val_3881_ = leanh::lean_ctor_get(v___x_3880_, 0);
                                        leanh::lean_inc(v_val_3881_);
                                        leanh::lean_dec_ref_known(v___x_3880_, 1);
                                        leanh::lean_inc(v_userName_3876_);
                                        leanh::lean_inc(v_fvarId_3875_);
                                        v___x_3882_ = l_Lean_LocalContext_mkAuxDecl(
                                            v_b_3860_,
                                            v_fvarId_3875_,
                                            v_userName_3876_,
                                            v_a_3879_,
                                            v_val_3881_,
                                        );
                                        v_a_3867_ = v___x_3882_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3880_);
                                        leanh::lean_dec(v_a_3879_);
                                        leanh::lean_dec_ref(v_b_3860_);
                                        v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0;
                                        v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1;
                                        v___x_3885_ = leanh::lean_unsigned_to_nat(635);
                                        v___x_3886_ = leanh::lean_unsigned_to_nat(12);
                                        v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2;
                                        v___x_3888_ = 1;
                                        leanh::lean_inc(v_userName_3876_);
                                        v___x_3889_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_3876_, v___x_3888_);
                                        v___x_3890_ = lean_string_append(v___x_3887_, v___x_3889_);
                                        leanh::lean_dec_ref(v___x_3889_);
                                        v___x_3891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3;
                                        v___x_3892_ = lean_string_append(v___x_3890_, v___x_3891_);
                                        v___x_3893_ = l_mkPanicMessageWithDecl(
                                            v___x_3883_,
                                            v___x_3884_,
                                            v___x_3885_,
                                            v___x_3886_,
                                            v___x_3892_,
                                        );
                                        leanh::lean_dec_ref(v___x_3892_);
                                        v___x_3894_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v___x_3893_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
                                        if leanh::lean_obj_tag(v___x_3894_) == 0 {
                                            v_a_3895_ = leanh::lean_ctor_get(v___x_3894_, 0);
                                            leanh::lean_inc(v_a_3895_);
                                            leanh::lean_dec_ref_known(v___x_3894_, 1);
                                            v_a_3867_ = v_a_3895_;
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_3894_;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_b_3860_);
                                    v_a_3896_ = leanh::lean_ctor_get(v___x_3878_, 0);
                                    v_isSharedCheck_3903_ =
                                        (!leanh::lean_is_exclusive(v___x_3878_)) as u8;
                                    if v_isSharedCheck_3903_ == 0 {
                                        v___x_3898_ = v___x_3878_;
                                        v_isShared_3899_ = v_isSharedCheck_3903_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3896_);
                                        leanh::lean_dec(v___x_3878_);
                                        v___x_3898_ = leanh::lean_box(0);
                                        v_isShared_3899_ = v_isSharedCheck_3903_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                v_fvarId_3904_ = leanh::lean_ctor_get(v_val_3873_, 1);
                                v_userName_3905_ = leanh::lean_ctor_get(v_val_3873_, 2);
                                v_type_3906_ = leanh::lean_ctor_get(v_val_3873_, 3);
                                v_bi_3907_ = leanh::lean_ctor_get_uint8(
                                    v_val_3873_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                leanh::lean_inc_ref(v_type_3906_);
                                v___x_3908_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_3906_, v___y_3862_);
                                if leanh::lean_obj_tag(v___x_3908_) == 0 {
                                    v_a_3909_ = leanh::lean_ctor_get(v___x_3908_, 0);
                                    leanh::lean_inc(v_a_3909_);
                                    leanh::lean_dec_ref_known(v___x_3908_, 1);
                                    leanh::lean_inc(v_userName_3905_);
                                    leanh::lean_inc(v_fvarId_3904_);
                                    v___x_3910_ = l_Lean_LocalContext_mkLocalDecl(
                                        v_b_3860_,
                                        v_fvarId_3904_,
                                        v_userName_3905_,
                                        v_a_3909_,
                                        v_bi_3907_,
                                        v_kind_3874_,
                                    );
                                    v_a_3867_ = v___x_3910_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_b_3860_);
                                    v_a_3911_ = leanh::lean_ctor_get(v___x_3908_, 0);
                                    v_isSharedCheck_3918_ =
                                        (!leanh::lean_is_exclusive(v___x_3908_)) as u8;
                                    if v_isSharedCheck_3918_ == 0 {
                                        v___x_3913_ = v___x_3908_;
                                        v_isShared_3914_ = v_isSharedCheck_3918_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3911_);
                                        leanh::lean_dec(v___x_3908_);
                                        v___x_3913_ = leanh::lean_box(0);
                                        v_isShared_3914_ = v_isSharedCheck_3918_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_fvarId_3919_ = leanh::lean_ctor_get(v_val_3873_, 1);
                            v_userName_3920_ = leanh::lean_ctor_get(v_val_3873_, 2);
                            v_type_3921_ = leanh::lean_ctor_get(v_val_3873_, 3);
                            v_value_3922_ = leanh::lean_ctor_get(v_val_3873_, 4);
                            v_nondep_3923_ = leanh::lean_ctor_get_uint8(
                                v_val_3873_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                            );
                            v_kind_3924_ = leanh::lean_ctor_get_uint8(
                                v_val_3873_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1)
                                    as u32,
                            );
                            leanh::lean_inc_ref(v_type_3921_);
                            v___x_3925_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_3921_, v___y_3862_);
                            if leanh::lean_obj_tag(v___x_3925_) == 0 {
                                v_a_3926_ = leanh::lean_ctor_get(v___x_3925_, 0);
                                leanh::lean_inc(v_a_3926_);
                                leanh::lean_dec_ref_known(v___x_3925_, 1);
                                leanh::lean_inc_ref(v_value_3922_);
                                v___x_3927_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_value_3922_, v___y_3862_);
                                if leanh::lean_obj_tag(v___x_3927_) == 0 {
                                    v_a_3928_ = leanh::lean_ctor_get(v___x_3927_, 0);
                                    leanh::lean_inc(v_a_3928_);
                                    leanh::lean_dec_ref_known(v___x_3927_, 1);
                                    leanh::lean_inc(v_userName_3920_);
                                    leanh::lean_inc(v_fvarId_3919_);
                                    v___x_3929_ = l_Lean_LocalContext_mkLetDecl(
                                        v_b_3860_,
                                        v_fvarId_3919_,
                                        v_userName_3920_,
                                        v_a_3926_,
                                        v_a_3928_,
                                        v_nondep_3923_,
                                        v_kind_3924_,
                                    );
                                    v_a_3867_ = v___x_3929_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_a_3926_);
                                    leanh::lean_dec_ref(v_b_3860_);
                                    v_a_3930_ = leanh::lean_ctor_get(v___x_3927_, 0);
                                    v_isSharedCheck_3937_ =
                                        (!leanh::lean_is_exclusive(v___x_3927_)) as u8;
                                    if v_isSharedCheck_3937_ == 0 {
                                        v___x_3932_ = v___x_3927_;
                                        v_isShared_3933_ = v_isSharedCheck_3937_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3930_);
                                        leanh::lean_dec(v___x_3927_);
                                        v___x_3932_ = leanh::lean_box(0);
                                        v_isShared_3933_ = v_isSharedCheck_3937_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_3860_);
                                v_a_3938_ = leanh::lean_ctor_get(v___x_3925_, 0);
                                v_isSharedCheck_3945_ =
                                    (!leanh::lean_is_exclusive(v___x_3925_)) as u8;
                                if v_isSharedCheck_3945_ == 0 {
                                    v___x_3940_ = v___x_3925_;
                                    v_isShared_3941_ = v_isSharedCheck_3945_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3938_);
                                    leanh::lean_dec(v___x_3925_);
                                    v___x_3940_ = leanh::lean_box(0);
                                    v_isShared_3941_ = v_isSharedCheck_3945_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_3946_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3946_, 0, v_b_3860_);
                    return v___x_3946_;
                }
            }
            1 => {
                v___x_3868_ = 1usize;
                v___x_3869_ = lean_usize_add(v_i_3858_, v___x_3868_);
                v_i_3858_ = v___x_3869_;
                v_b_3860_ = v_a_3867_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3899_ == 0 {
                    v___x_3901_ = v___x_3898_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
                    v___x_3901_ = v_reuseFailAlloc_3902_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3901_;
            }
            4 => {
                if v_isShared_3914_ == 0 {
                    v___x_3916_ = v___x_3913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3916_;
            }
            6 => {
                if v_isShared_3933_ == 0 {
                    v___x_3935_ = v___x_3932_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
                    v___x_3935_ = v_reuseFailAlloc_3936_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3935_;
            }
            8 => {
                if v_isShared_3941_ == 0 {
                    v___x_3943_ = v___x_3940_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3944_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
                    v___x_3943_ = v_reuseFailAlloc_3944_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___boxed(
    mut v_auxDeclToFullName_3947_: *mut leanh::LeanObject,
    mut v_as_3948_: *mut leanh::LeanObject,
    mut v_i_3949_: *mut leanh::LeanObject,
    mut v_stop_3950_: *mut leanh::LeanObject,
    mut v_b_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
    mut v___y_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3957_: usize = 0;
    let mut v_stop_boxed_3958_: usize = 0;
    let mut v_res_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3957_ = leanh::lean_unbox_usize(v_i_3949_);
    leanh::lean_dec(v_i_3949_);
    v_stop_boxed_3958_ = leanh::lean_unbox_usize(v_stop_3950_);
    leanh::lean_dec(v_stop_3950_);
    v_res_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_3947_, v_as_3948_, v_i_boxed_3957_, v_stop_boxed_3958_, v_b_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    leanh::lean_dec(v___y_3955_);
    leanh::lean_dec_ref(v___y_3954_);
    leanh::lean_dec(v___y_3953_);
    leanh::lean_dec_ref(v___y_3952_);
    leanh::lean_dec_ref(v_as_3948_);
    leanh::lean_dec(v_auxDeclToFullName_3947_);
    return v_res_3959_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(
    mut v_auxDeclToFullName_3960_: *mut leanh::LeanObject,
    mut v_x_3961_: *mut leanh::LeanObject,
    mut v_x_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: u8 = 0;
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: usize = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut v_vs_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: u8 = 0;
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: usize = 0;
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: usize = 0;
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3961_) == 0 {
                    v_cs_3968_ = leanh::lean_ctor_get(v_x_3961_, 0);
                    v_isSharedCheck_3988_ = (!leanh::lean_is_exclusive(v_x_3961_)) as u8;
                    if v_isSharedCheck_3988_ == 0 {
                        v___x_3970_ = v_x_3961_;
                        v_isShared_3971_ = v_isSharedCheck_3988_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_3968_);
                        leanh::lean_dec(v_x_3961_);
                        v___x_3970_ = leanh::lean_box(0);
                        v_isShared_3971_ = v_isSharedCheck_3988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_3989_ = leanh::lean_ctor_get(v_x_3961_, 0);
                    v_isSharedCheck_4009_ = (!leanh::lean_is_exclusive(v_x_3961_)) as u8;
                    if v_isSharedCheck_4009_ == 0 {
                        v___x_3991_ = v_x_3961_;
                        v_isShared_3992_ = v_isSharedCheck_4009_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3989_);
                        leanh::lean_dec(v_x_3961_);
                        v___x_3991_ = leanh::lean_box(0);
                        v_isShared_3992_ = v_isSharedCheck_4009_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3972_ = leanh::lean_unsigned_to_nat(0);
                v___x_3973_ = lean_array_get_size(v_cs_3968_);
                v___x_3974_ = lean_nat_dec_lt(v___x_3972_, v___x_3973_);
                if v___x_3974_ == 0 {
                    leanh::lean_dec_ref(v_cs_3968_);
                    if v_isShared_3971_ == 0 {
                        leanh::lean_ctor_set(v___x_3970_, 0, v_x_3962_);
                        v___x_3976_ = v___x_3970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3977_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_x_3962_);
                        v___x_3976_ = v_reuseFailAlloc_3977_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3978_ = lean_nat_dec_le(v___x_3973_, v___x_3973_);
                    if v___x_3978_ == 0 {
                        if v___x_3974_ == 0 {
                            leanh::lean_dec_ref(v_cs_3968_);
                            if v_isShared_3971_ == 0 {
                                leanh::lean_ctor_set(v___x_3970_, 0, v_x_3962_);
                                v___x_3980_ = v___x_3970_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3981_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_x_3962_);
                                v___x_3980_ = v_reuseFailAlloc_3981_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3970_);
                            v___x_3982_ = 0usize;
                            v___x_3983_ = lean_usize_of_nat(v___x_3973_);
                            v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_3960_, v_cs_3968_, v___x_3982_, v___x_3983_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                            leanh::lean_dec_ref(v_cs_3968_);
                            return v___x_3984_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3970_);
                        v___x_3985_ = 0usize;
                        v___x_3986_ = lean_usize_of_nat(v___x_3973_);
                        v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_3960_, v_cs_3968_, v___x_3985_, v___x_3986_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                        leanh::lean_dec_ref(v_cs_3968_);
                        return v___x_3987_;
                    }
                }
            }
            2 => {
                return v___x_3976_;
            }
            3 => {
                return v___x_3980_;
            }
            4 => {
                v___x_3993_ = leanh::lean_unsigned_to_nat(0);
                v___x_3994_ = lean_array_get_size(v_vs_3989_);
                v___x_3995_ = lean_nat_dec_lt(v___x_3993_, v___x_3994_);
                if v___x_3995_ == 0 {
                    leanh::lean_dec_ref(v_vs_3989_);
                    if v_isShared_3992_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3991_, 0);
                        leanh::lean_ctor_set(v___x_3991_, 0, v_x_3962_);
                        v___x_3997_ = v___x_3991_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_x_3962_);
                        v___x_3997_ = v_reuseFailAlloc_3998_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3999_ = lean_nat_dec_le(v___x_3994_, v___x_3994_);
                    if v___x_3999_ == 0 {
                        if v___x_3995_ == 0 {
                            leanh::lean_dec_ref(v_vs_3989_);
                            if v_isShared_3992_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_3991_, 0);
                                leanh::lean_ctor_set(v___x_3991_, 0, v_x_3962_);
                                v___x_4001_ = v___x_3991_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_4002_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_x_3962_);
                                v___x_4001_ = v_reuseFailAlloc_4002_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3991_);
                            v___x_4003_ = 0usize;
                            v___x_4004_ = lean_usize_of_nat(v___x_3994_);
                            v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_3960_, v_vs_3989_, v___x_4003_, v___x_4004_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                            leanh::lean_dec_ref(v_vs_3989_);
                            return v___x_4005_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3991_);
                        v___x_4006_ = 0usize;
                        v___x_4007_ = lean_usize_of_nat(v___x_3994_);
                        v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_3960_, v_vs_3989_, v___x_4006_, v___x_4007_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                        leanh::lean_dec_ref(v_vs_3989_);
                        return v___x_4008_;
                    }
                }
            }
            5 => {
                return v___x_3997_;
            }
            6 => {
                return v___x_4001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(
    mut v_auxDeclToFullName_4010_: *mut leanh::LeanObject,
    mut v_as_4011_: *mut leanh::LeanObject,
    mut v_i_4012_: usize,
    mut v_stop_4013_: usize,
    mut v_b_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
    mut v___y_4016_: *mut leanh::LeanObject,
    mut v___y_4017_: *mut leanh::LeanObject,
    mut v___y_4018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: usize = 0;
    let mut v___x_4025_: usize = 0;
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4020_ = lean_usize_dec_eq(v_i_4012_, v_stop_4013_);
                if v___x_4020_ == 0 {
                    v___x_4021_ = lean_array_uget_borrowed(v_as_4011_, v_i_4012_);
                    leanh::lean_inc(v___x_4021_);
                    v___x_4022_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_4010_, v___x_4021_, v_b_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
                    if leanh::lean_obj_tag(v___x_4022_) == 0 {
                        v_a_4023_ = leanh::lean_ctor_get(v___x_4022_, 0);
                        leanh::lean_inc(v_a_4023_);
                        leanh::lean_dec_ref_known(v___x_4022_, 1);
                        v___x_4024_ = 1usize;
                        v___x_4025_ = lean_usize_add(v_i_4012_, v___x_4024_);
                        v_i_4012_ = v___x_4025_;
                        v_b_4014_ = v_a_4023_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4022_;
                    }
                } else {
                    v___x_4027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4027_, 0, v_b_4014_);
                    return v___x_4027_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_auxDeclToFullName_4028_: *mut leanh::LeanObject,
    mut v_as_4029_: *mut leanh::LeanObject,
    mut v_i_4030_: *mut leanh::LeanObject,
    mut v_stop_4031_: *mut leanh::LeanObject,
    mut v_b_4032_: *mut leanh::LeanObject,
    mut v___y_4033_: *mut leanh::LeanObject,
    mut v___y_4034_: *mut leanh::LeanObject,
    mut v___y_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
    mut v___y_4037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4038_: usize = 0;
    let mut v_stop_boxed_4039_: usize = 0;
    let mut v_res_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4038_ = leanh::lean_unbox_usize(v_i_4030_);
    leanh::lean_dec(v_i_4030_);
    v_stop_boxed_4039_ = leanh::lean_unbox_usize(v_stop_4031_);
    leanh::lean_dec(v_stop_4031_);
    v_res_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_4028_, v_as_4029_, v_i_boxed_4038_, v_stop_boxed_4039_, v_b_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
    leanh::lean_dec(v___y_4036_);
    leanh::lean_dec_ref(v___y_4035_);
    leanh::lean_dec(v___y_4034_);
    leanh::lean_dec_ref(v___y_4033_);
    leanh::lean_dec_ref(v_as_4029_);
    leanh::lean_dec(v_auxDeclToFullName_4028_);
    return v_res_4040_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(
    mut v_auxDeclToFullName_4041_: *mut leanh::LeanObject,
    mut v_x_4042_: *mut leanh::LeanObject,
    mut v_x_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_4041_, v_x_4042_, v_x_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
    leanh::lean_dec(v___y_4047_);
    leanh::lean_dec_ref(v___y_4046_);
    leanh::lean_dec(v___y_4045_);
    leanh::lean_dec_ref(v___y_4044_);
    leanh::lean_dec(v_auxDeclToFullName_4041_);
    return v_res_4049_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_4050_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(
    mut v_auxDeclToFullName_4051_: *mut leanh::LeanObject,
    mut v_x_4052_: *mut leanh::LeanObject,
    mut v_x_4053_: usize,
    mut v_x_4054_: usize,
    mut v_x_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: usize = 0;
    let mut v_j_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: usize = 0;
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: usize = 0;
    let mut v___x_4069_: usize = 0;
    let mut v___x_4070_: usize = 0;
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: usize = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: usize = 0;
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4088_: u8 = 0;
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: u8 = 0;
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: usize = 0;
    let mut v___x_4100_: usize = 0;
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: usize = 0;
    let mut v___x_4103_: usize = 0;
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4052_) == 0 {
                    v_cs_4061_ = leanh::lean_ctor_get(v_x_4052_, 0);
                    leanh::lean_inc_ref(v_cs_4061_);
                    leanh::lean_dec_ref_known(v_x_4052_, 1);
                    v___x_4062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0);
                    v___x_4063_ = lean_usize_shift_right(v_x_4053_, v_x_4054_);
                    v_j_4064_ = lean_usize_to_nat(v___x_4063_);
                    v___x_4065_ = lean_array_get_borrowed(v___x_4062_, v_cs_4061_, v_j_4064_);
                    v___x_4066_ = 1usize;
                    v___x_4067_ = lean_usize_shift_left(v___x_4066_, v_x_4054_);
                    v___x_4068_ = lean_usize_sub(v___x_4067_, v___x_4066_);
                    v___x_4069_ = lean_usize_land(v_x_4053_, v___x_4068_);
                    v___x_4070_ = 5usize;
                    v___x_4071_ = lean_usize_sub(v_x_4054_, v___x_4070_);
                    leanh::lean_inc(v___x_4065_);
                    v___x_4072_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_4051_, v___x_4065_, v___x_4069_, v___x_4071_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                    if leanh::lean_obj_tag(v___x_4072_) == 0 {
                        v_a_4073_ = leanh::lean_ctor_get(v___x_4072_, 0);
                        leanh::lean_inc(v_a_4073_);
                        v___x_4074_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4075_ = lean_nat_add(v_j_4064_, v___x_4074_);
                        leanh::lean_dec(v_j_4064_);
                        v___x_4076_ = lean_array_get_size(v_cs_4061_);
                        v___x_4077_ = lean_nat_dec_lt(v___x_4075_, v___x_4076_);
                        if v___x_4077_ == 0 {
                            leanh::lean_dec(v___x_4075_);
                            leanh::lean_dec(v_a_4073_);
                            leanh::lean_dec_ref(v_cs_4061_);
                            return v___x_4072_;
                        } else {
                            v___x_4078_ = lean_nat_dec_le(v___x_4076_, v___x_4076_);
                            if v___x_4078_ == 0 {
                                if v___x_4077_ == 0 {
                                    leanh::lean_dec(v___x_4075_);
                                    leanh::lean_dec(v_a_4073_);
                                    leanh::lean_dec_ref(v_cs_4061_);
                                    return v___x_4072_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_4072_, 1);
                                    v___x_4079_ = lean_usize_of_nat(v___x_4075_);
                                    leanh::lean_dec(v___x_4075_);
                                    v___x_4080_ = lean_usize_of_nat(v___x_4076_);
                                    v___x_4081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_4051_, v_cs_4061_, v___x_4079_, v___x_4080_, v_a_4073_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                                    leanh::lean_dec_ref(v_cs_4061_);
                                    return v___x_4081_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v___x_4072_, 1);
                                v___x_4082_ = lean_usize_of_nat(v___x_4075_);
                                leanh::lean_dec(v___x_4075_);
                                v___x_4083_ = lean_usize_of_nat(v___x_4076_);
                                v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_4051_, v_cs_4061_, v___x_4082_, v___x_4083_, v_a_4073_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                                leanh::lean_dec_ref(v_cs_4061_);
                                return v___x_4084_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_j_4064_);
                        leanh::lean_dec_ref(v_cs_4061_);
                        return v___x_4072_;
                    }
                } else {
                    v_vs_4085_ = leanh::lean_ctor_get(v_x_4052_, 0);
                    v_isSharedCheck_4105_ = (!leanh::lean_is_exclusive(v_x_4052_)) as u8;
                    if v_isSharedCheck_4105_ == 0 {
                        v___x_4087_ = v_x_4052_;
                        v_isShared_4088_ = v_isSharedCheck_4105_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4085_);
                        leanh::lean_dec(v_x_4052_);
                        v___x_4087_ = leanh::lean_box(0);
                        v_isShared_4088_ = v_isSharedCheck_4105_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4089_ = lean_usize_to_nat(v_x_4053_);
                v___x_4090_ = lean_array_get_size(v_vs_4085_);
                v___x_4091_ = lean_nat_dec_lt(v___x_4089_, v___x_4090_);
                if v___x_4091_ == 0 {
                    leanh::lean_dec(v___x_4089_);
                    leanh::lean_dec_ref(v_vs_4085_);
                    if v_isShared_4088_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4087_, 0);
                        leanh::lean_ctor_set(v___x_4087_, 0, v_x_4055_);
                        v___x_4093_ = v___x_4087_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_x_4055_);
                        v___x_4093_ = v_reuseFailAlloc_4094_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4095_ = lean_nat_dec_le(v___x_4090_, v___x_4090_);
                    if v___x_4095_ == 0 {
                        if v___x_4091_ == 0 {
                            leanh::lean_dec(v___x_4089_);
                            leanh::lean_dec_ref(v_vs_4085_);
                            if v_isShared_4088_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_4087_, 0);
                                leanh::lean_ctor_set(v___x_4087_, 0, v_x_4055_);
                                v___x_4097_ = v___x_4087_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4098_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_x_4055_);
                                v___x_4097_ = v_reuseFailAlloc_4098_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_4087_);
                            v___x_4099_ = lean_usize_of_nat(v___x_4089_);
                            leanh::lean_dec(v___x_4089_);
                            v___x_4100_ = lean_usize_of_nat(v___x_4090_);
                            v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4051_, v_vs_4085_, v___x_4099_, v___x_4100_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                            leanh::lean_dec_ref(v_vs_4085_);
                            return v___x_4101_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4087_);
                        v___x_4102_ = lean_usize_of_nat(v___x_4089_);
                        leanh::lean_dec(v___x_4089_);
                        v___x_4103_ = lean_usize_of_nat(v___x_4090_);
                        v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4051_, v_vs_4085_, v___x_4102_, v___x_4103_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                        leanh::lean_dec_ref(v_vs_4085_);
                        return v___x_4104_;
                    }
                }
            }
            2 => {
                return v___x_4093_;
            }
            3 => {
                return v___x_4097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___boxed(
    mut v_auxDeclToFullName_4106_: *mut leanh::LeanObject,
    mut v_x_4107_: *mut leanh::LeanObject,
    mut v_x_4108_: *mut leanh::LeanObject,
    mut v_x_4109_: *mut leanh::LeanObject,
    mut v_x_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4510__boxed_4116_: usize = 0;
    let mut v_x_4511__boxed_4117_: usize = 0;
    let mut v_res_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4510__boxed_4116_ = leanh::lean_unbox_usize(v_x_4108_);
    leanh::lean_dec(v_x_4108_);
    v_x_4511__boxed_4117_ = leanh::lean_unbox_usize(v_x_4109_);
    leanh::lean_dec(v_x_4109_);
    v_res_4118_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_4106_, v_x_4107_, v_x_4510__boxed_4116_, v_x_4511__boxed_4117_, v_x_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
    leanh::lean_dec(v___y_4114_);
    leanh::lean_dec_ref(v___y_4113_);
    leanh::lean_dec(v___y_4112_);
    leanh::lean_dec_ref(v___y_4111_);
    leanh::lean_dec(v_auxDeclToFullName_4106_);
    return v_res_4118_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(
    mut v_auxDeclToFullName_4119_: *mut leanh::LeanObject,
    mut v_t_4120_: *mut leanh::LeanObject,
    mut v_init_4121_: *mut leanh::LeanObject,
    mut v_start_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: u8 = 0;
    v___x_4128_ = leanh::lean_unsigned_to_nat(0);
    v___x_4129_ = lean_nat_dec_eq(v_start_4122_, v___x_4128_);
    if v___x_4129_ == 0 {
        let mut v_root_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_4132_: usize = 0;
        let mut v_tailOff_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4134_: u8 = 0;
        v_root_4130_ = leanh::lean_ctor_get(v_t_4120_, 0);
        leanh::lean_inc_ref(v_root_4130_);
        v_tail_4131_ = leanh::lean_ctor_get(v_t_4120_, 1);
        leanh::lean_inc_ref(v_tail_4131_);
        v_shift_4132_ = leanh::lean_ctor_get_usize(v_t_4120_, 4);
        v_tailOff_4133_ = leanh::lean_ctor_get(v_t_4120_, 3);
        leanh::lean_inc(v_tailOff_4133_);
        leanh::lean_dec_ref(v_t_4120_);
        v___x_4134_ = lean_nat_dec_le(v_tailOff_4133_, v_start_4122_);
        if v___x_4134_ == 0 {
            let mut v___x_4135_: usize = 0;
            let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_tailOff_4133_);
            v___x_4135_ = lean_usize_of_nat(v_start_4122_);
            v___x_4136_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_4119_, v_root_4130_, v___x_4135_, v_shift_4132_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
            if leanh::lean_obj_tag(v___x_4136_) == 0 {
                let mut v_a_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4139_: u8 = 0;
                v_a_4137_ = leanh::lean_ctor_get(v___x_4136_, 0);
                leanh::lean_inc(v_a_4137_);
                v___x_4138_ = lean_array_get_size(v_tail_4131_);
                v___x_4139_ = lean_nat_dec_lt(v___x_4128_, v___x_4138_);
                if v___x_4139_ == 0 {
                    leanh::lean_dec(v_a_4137_);
                    leanh::lean_dec_ref(v_tail_4131_);
                    return v___x_4136_;
                } else {
                    let mut v___x_4140_: u8 = 0;
                    v___x_4140_ = lean_nat_dec_le(v___x_4138_, v___x_4138_);
                    if v___x_4140_ == 0 {
                        if v___x_4139_ == 0 {
                            leanh::lean_dec(v_a_4137_);
                            leanh::lean_dec_ref(v_tail_4131_);
                            return v___x_4136_;
                        } else {
                            let mut v___x_4141_: usize = 0;
                            let mut v___x_4142_: usize = 0;
                            let mut v___x_4143_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec_ref_known(v___x_4136_, 1);
                            v___x_4141_ = 0usize;
                            v___x_4142_ = lean_usize_of_nat(v___x_4138_);
                            v___x_4143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4141_, v___x_4142_, v_a_4137_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                            leanh::lean_dec_ref(v_tail_4131_);
                            return v___x_4143_;
                        }
                    } else {
                        let mut v___x_4144_: usize = 0;
                        let mut v___x_4145_: usize = 0;
                        let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec_ref_known(v___x_4136_, 1);
                        v___x_4144_ = 0usize;
                        v___x_4145_ = lean_usize_of_nat(v___x_4138_);
                        v___x_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4144_, v___x_4145_, v_a_4137_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        leanh::lean_dec_ref(v_tail_4131_);
                        return v___x_4146_;
                    }
                }
            } else {
                leanh::lean_dec_ref(v_tail_4131_);
                return v___x_4136_;
            }
        } else {
            let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4149_: u8 = 0;
            leanh::lean_dec_ref(v_root_4130_);
            v___x_4147_ = lean_nat_sub(v_start_4122_, v_tailOff_4133_);
            leanh::lean_dec(v_tailOff_4133_);
            v___x_4148_ = lean_array_get_size(v_tail_4131_);
            v___x_4149_ = lean_nat_dec_lt(v___x_4147_, v___x_4148_);
            if v___x_4149_ == 0 {
                let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_4147_);
                leanh::lean_dec_ref(v_tail_4131_);
                v___x_4150_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4150_, 0, v_init_4121_);
                return v___x_4150_;
            } else {
                let mut v___x_4151_: u8 = 0;
                v___x_4151_ = lean_nat_dec_le(v___x_4148_, v___x_4148_);
                if v___x_4151_ == 0 {
                    if v___x_4149_ == 0 {
                        let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_4147_);
                        leanh::lean_dec_ref(v_tail_4131_);
                        v___x_4152_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4152_, 0, v_init_4121_);
                        return v___x_4152_;
                    } else {
                        let mut v___x_4153_: usize = 0;
                        let mut v___x_4154_: usize = 0;
                        let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4153_ = lean_usize_of_nat(v___x_4147_);
                        leanh::lean_dec(v___x_4147_);
                        v___x_4154_ = lean_usize_of_nat(v___x_4148_);
                        v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4153_, v___x_4154_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        leanh::lean_dec_ref(v_tail_4131_);
                        return v___x_4155_;
                    }
                } else {
                    let mut v___x_4156_: usize = 0;
                    let mut v___x_4157_: usize = 0;
                    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4156_ = lean_usize_of_nat(v___x_4147_);
                    leanh::lean_dec(v___x_4147_);
                    v___x_4157_ = lean_usize_of_nat(v___x_4148_);
                    v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4156_, v___x_4157_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                    leanh::lean_dec_ref(v_tail_4131_);
                    return v___x_4158_;
                }
            }
        }
    } else {
        let mut v_root_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_root_4159_ = leanh::lean_ctor_get(v_t_4120_, 0);
        leanh::lean_inc_ref(v_root_4159_);
        v_tail_4160_ = leanh::lean_ctor_get(v_t_4120_, 1);
        leanh::lean_inc_ref(v_tail_4160_);
        leanh::lean_dec_ref(v_t_4120_);
        v___x_4161_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_4119_, v_root_4159_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
        if leanh::lean_obj_tag(v___x_4161_) == 0 {
            let mut v_a_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4164_: u8 = 0;
            v_a_4162_ = leanh::lean_ctor_get(v___x_4161_, 0);
            leanh::lean_inc(v_a_4162_);
            v___x_4163_ = lean_array_get_size(v_tail_4160_);
            v___x_4164_ = lean_nat_dec_lt(v___x_4128_, v___x_4163_);
            if v___x_4164_ == 0 {
                leanh::lean_dec(v_a_4162_);
                leanh::lean_dec_ref(v_tail_4160_);
                return v___x_4161_;
            } else {
                let mut v___x_4165_: u8 = 0;
                v___x_4165_ = lean_nat_dec_le(v___x_4163_, v___x_4163_);
                if v___x_4165_ == 0 {
                    if v___x_4164_ == 0 {
                        leanh::lean_dec(v_a_4162_);
                        leanh::lean_dec_ref(v_tail_4160_);
                        return v___x_4161_;
                    } else {
                        let mut v___x_4166_: usize = 0;
                        let mut v___x_4167_: usize = 0;
                        let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec_ref_known(v___x_4161_, 1);
                        v___x_4166_ = 0usize;
                        v___x_4167_ = lean_usize_of_nat(v___x_4163_);
                        v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4160_, v___x_4166_, v___x_4167_, v_a_4162_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        leanh::lean_dec_ref(v_tail_4160_);
                        return v___x_4168_;
                    }
                } else {
                    let mut v___x_4169_: usize = 0;
                    let mut v___x_4170_: usize = 0;
                    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref_known(v___x_4161_, 1);
                    v___x_4169_ = 0usize;
                    v___x_4170_ = lean_usize_of_nat(v___x_4163_);
                    v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4160_, v___x_4169_, v___x_4170_, v_a_4162_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                    leanh::lean_dec_ref(v_tail_4160_);
                    return v___x_4171_;
                }
            }
        } else {
            leanh::lean_dec_ref(v_tail_4160_);
            return v___x_4161_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(
    mut v_auxDeclToFullName_4172_: *mut leanh::LeanObject,
    mut v_t_4173_: *mut leanh::LeanObject,
    mut v_init_4174_: *mut leanh::LeanObject,
    mut v_start_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
    mut v___y_4178_: *mut leanh::LeanObject,
    mut v___y_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_4172_, v_t_4173_, v_init_4174_, v_start_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
    leanh::lean_dec(v___y_4179_);
    leanh::lean_dec_ref(v___y_4178_);
    leanh::lean_dec(v___y_4177_);
    leanh::lean_dec_ref(v___y_4176_);
    leanh::lean_dec(v_start_4175_);
    leanh::lean_dec(v_auxDeclToFullName_4172_);
    return v_res_4181_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(
    mut v_auxDeclToFullName_4182_: *mut leanh::LeanObject,
    mut v_lctx_4183_: *mut leanh::LeanObject,
    mut v_init_4184_: *mut leanh::LeanObject,
    mut v_start_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_decls_4191_ = leanh::lean_ctor_get(v_lctx_4183_, 1);
    leanh::lean_inc_ref(v_decls_4191_);
    leanh::lean_dec_ref(v_lctx_4183_);
    v___x_4192_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_4182_, v_decls_4191_, v_init_4184_, v_start_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
    return v___x_4192_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(
    mut v_auxDeclToFullName_4193_: *mut leanh::LeanObject,
    mut v_lctx_4194_: *mut leanh::LeanObject,
    mut v_init_4195_: *mut leanh::LeanObject,
    mut v_start_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_4193_, v_lctx_4194_, v_init_4195_, v_start_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec_ref(v___y_4199_);
    leanh::lean_dec(v___y_4198_);
    leanh::lean_dec_ref(v___y_4197_);
    leanh::lean_dec(v_start_4196_);
    leanh::lean_dec(v_auxDeclToFullName_4193_);
    return v_res_4202_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4203_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4204_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0);
    v___x_4205_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
    return v___x_4205_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = leanh::lean_unsigned_to_nat(32);
    v___x_4207_ = lean_mk_empty_array_with_capacity(v___x_4206_);
    v___x_4208_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4208_, 0, v___x_4207_);
    return v___x_4208_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4209_: usize = 0;
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = 5usize;
    v___x_4210_ = leanh::lean_unsigned_to_nat(0);
    v___x_4211_ = leanh::lean_unsigned_to_nat(32);
    v___x_4212_ = lean_mk_empty_array_with_capacity(v___x_4211_);
    v___x_4213_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2);
    v___x_4214_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
    leanh::lean_ctor_set(v___x_4214_, 1, v___x_4212_);
    leanh::lean_ctor_set(v___x_4214_, 2, v___x_4210_);
    leanh::lean_ctor_set(v___x_4214_, 3, v___x_4210_);
    leanh::lean_ctor_set_usize(v___x_4214_, 4, v___x_4209_);
    return v___x_4214_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4215_ = leanh::lean_box(1);
    v___x_4216_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3);
    v___x_4217_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1);
    v___x_4218_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4218_, 0, v___x_4217_);
    leanh::lean_ctor_set(v___x_4218_, 1, v___x_4216_);
    leanh::lean_ctor_set(v___x_4218_, 2, v___x_4215_);
    return v___x_4218_;
}
pub unsafe fn l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(
    mut v_lctx_4219_: *mut leanh::LeanObject,
    mut v___y_4220_: *mut leanh::LeanObject,
    mut v___y_4221_: *mut leanh::LeanObject,
    mut v___y_4222_: *mut leanh::LeanObject,
    mut v___y_4223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_auxDeclToFullName_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_auxDeclToFullName_4225_ = leanh::lean_ctor_get(v_lctx_4219_, 2);
    leanh::lean_inc(v_auxDeclToFullName_4225_);
    v___x_4226_ = leanh::lean_unsigned_to_nat(0);
    v___x_4227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4);
    v___x_4228_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_4225_, v_lctx_4219_, v___x_4227_, v___x_4226_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
    leanh::lean_dec(v_auxDeclToFullName_4225_);
    return v___x_4228_;
}
pub unsafe fn l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(
    mut v_lctx_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4235_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(
        v_lctx_4229_,
        v___y_4230_,
        v___y_4231_,
        v___y_4232_,
        v___y_4233_,
    );
    leanh::lean_dec(v___y_4233_);
    leanh::lean_dec_ref(v___y_4232_);
    leanh::lean_dec(v___y_4231_);
    leanh::lean_dec_ref(v___y_4230_);
    return v_res_4235_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(
    mut v_x_4236_: *mut leanh::LeanObject,
    mut v_x_4237_: *mut leanh::LeanObject,
    mut v_x_4238_: *mut leanh::LeanObject,
    mut v_x_4239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u8 = 0;
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4240_ = leanh::lean_ctor_get(v_x_4236_, 0);
                v_vs_4241_ = leanh::lean_ctor_get(v_x_4236_, 1);
                v_isSharedCheck_4265_ = (!leanh::lean_is_exclusive(v_x_4236_)) as u8;
                if v_isSharedCheck_4265_ == 0 {
                    v___x_4243_ = v_x_4236_;
                    v_isShared_4244_ = v_isSharedCheck_4265_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4241_);
                    leanh::lean_inc(v_ks_4240_);
                    leanh::lean_dec(v_x_4236_);
                    v___x_4243_ = leanh::lean_box(0);
                    v_isShared_4244_ = v_isSharedCheck_4265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4245_ = lean_array_get_size(v_ks_4240_);
                v___x_4246_ = lean_nat_dec_lt(v_x_4237_, v___x_4245_);
                if v___x_4246_ == 0 {
                    leanh::lean_dec(v_x_4237_);
                    v___x_4247_ = lean_array_push(v_ks_4240_, v_x_4238_);
                    v___x_4248_ = lean_array_push(v_vs_4241_, v_x_4239_);
                    if v_isShared_4244_ == 0 {
                        leanh::lean_ctor_set(v___x_4243_, 1, v___x_4248_);
                        leanh::lean_ctor_set(v___x_4243_, 0, v___x_4247_);
                        v___x_4250_ = v___x_4243_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4251_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4247_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 1, v___x_4248_);
                        v___x_4250_ = v_reuseFailAlloc_4251_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4252_ = lean_array_fget_borrowed(v_ks_4240_, v_x_4237_);
                    v___x_4253_ = l_Lean_instBEqMVarId_beq(v_x_4238_, v_k_x27_4252_);
                    if v___x_4253_ == 0 {
                        if v_isShared_4244_ == 0 {
                            v___x_4255_ = v___x_4243_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4259_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_ks_4240_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_vs_4241_);
                            v___x_4255_ = v_reuseFailAlloc_4259_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4260_ = lean_array_fset(v_ks_4240_, v_x_4237_, v_x_4238_);
                        v___x_4261_ = lean_array_fset(v_vs_4241_, v_x_4237_, v_x_4239_);
                        leanh::lean_dec(v_x_4237_);
                        if v_isShared_4244_ == 0 {
                            leanh::lean_ctor_set(v___x_4243_, 1, v___x_4261_);
                            leanh::lean_ctor_set(v___x_4243_, 0, v___x_4260_);
                            v___x_4263_ = v___x_4243_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4264_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4260_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4261_);
                            v___x_4263_ = v_reuseFailAlloc_4264_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4250_;
            }
            3 => {
                v___x_4256_ = leanh::lean_unsigned_to_nat(1);
                v___x_4257_ = lean_nat_add(v_x_4237_, v___x_4256_);
                leanh::lean_dec(v_x_4237_);
                v_x_4236_ = v___x_4255_;
                v_x_4237_ = v___x_4257_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(
    mut v_n_4266_: *mut leanh::LeanObject,
    mut v_k_4267_: *mut leanh::LeanObject,
    mut v_v_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = leanh::lean_unsigned_to_nat(0);
    v___x_4270_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_n_4266_, v___x_4269_, v_k_4267_, v_v_4268_);
    return v___x_4270_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_4271_: usize = 0;
    let mut v___x_4272_: usize = 0;
    let mut v___x_4273_: usize = 0;
    v___x_4271_ = 5usize;
    v___x_4272_ = 1usize;
    v___x_4273_ = lean_usize_shift_left(v___x_4272_, v___x_4271_);
    return v___x_4273_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: usize = 0;
    let mut v___x_4276_: usize = 0;
    v___x_4274_ = 1usize;
    v___x_4275_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
    v___x_4276_ = lean_usize_sub(v___x_4275_, v___x_4274_);
    return v___x_4276_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4277_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4277_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(
    mut v_x_4278_: *mut leanh::LeanObject,
    mut v_x_4279_: usize,
    mut v_x_4280_: usize,
    mut v_x_4281_: *mut leanh::LeanObject,
    mut v_x_4282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: usize = 0;
    let mut v___x_4285_: usize = 0;
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: usize = 0;
    let mut v_j_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v_v_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v_node_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4319_: usize = 0;
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4325_: u8 = 0;
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4327_: u8 = 0;
    let mut v_unused_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: u8 = 0;
    let mut v_ks_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: usize = 0;
    let mut v___x_4345_: u8 = 0;
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: u8 = 0;
    let mut v_reuseFailAlloc_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4278_) == 0 {
                    v_es_4283_ = leanh::lean_ctor_get(v_x_4278_, 0);
                    v___x_4284_ = 5usize;
                    v___x_4285_ = 1usize;
                    v___x_4286_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1);
                    v___x_4287_ = lean_usize_land(v_x_4279_, v___x_4286_);
                    v_j_4288_ = lean_usize_to_nat(v___x_4287_);
                    v___x_4289_ = lean_array_get_size(v_es_4283_);
                    v___x_4290_ = lean_nat_dec_lt(v_j_4288_, v___x_4289_);
                    if v___x_4290_ == 0 {
                        leanh::lean_dec(v_j_4288_);
                        leanh::lean_dec(v_x_4282_);
                        leanh::lean_dec(v_x_4281_);
                        return v_x_4278_;
                    } else {
                        leanh::lean_inc_ref(v_es_4283_);
                        v_isSharedCheck_4327_ = (!leanh::lean_is_exclusive(v_x_4278_)) as u8;
                        if v_isSharedCheck_4327_ == 0 {
                            v_unused_4328_ = leanh::lean_ctor_get(v_x_4278_, 0);
                            leanh::lean_dec(v_unused_4328_);
                            v___x_4292_ = v_x_4278_;
                            v_isShared_4293_ = v_isSharedCheck_4327_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4278_);
                            v___x_4292_ = leanh::lean_box(0);
                            v_isShared_4293_ = v_isSharedCheck_4327_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4329_ = leanh::lean_ctor_get(v_x_4278_, 0);
                    v_vs_4330_ = leanh::lean_ctor_get(v_x_4278_, 1);
                    v_isSharedCheck_4350_ = (!leanh::lean_is_exclusive(v_x_4278_)) as u8;
                    if v_isSharedCheck_4350_ == 0 {
                        v___x_4332_ = v_x_4278_;
                        v_isShared_4333_ = v_isSharedCheck_4350_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4330_);
                        leanh::lean_inc(v_ks_4329_);
                        leanh::lean_dec(v_x_4278_);
                        v___x_4332_ = leanh::lean_box(0);
                        v_isShared_4333_ = v_isSharedCheck_4350_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4294_ = lean_array_fget(v_es_4283_, v_j_4288_);
                v___x_4295_ = leanh::lean_box(0);
                v_xs_x27_4296_ = lean_array_fset(v_es_4283_, v_j_4288_, v___x_4295_);
                match leanh::lean_obj_tag(v_v_4294_) {
                    0 => {
                        v_key_4303_ = leanh::lean_ctor_get(v_v_4294_, 0);
                        v_val_4304_ = leanh::lean_ctor_get(v_v_4294_, 1);
                        v_isSharedCheck_4314_ = (!leanh::lean_is_exclusive(v_v_4294_)) as u8;
                        if v_isSharedCheck_4314_ == 0 {
                            v___x_4306_ = v_v_4294_;
                            v_isShared_4307_ = v_isSharedCheck_4314_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4304_);
                            leanh::lean_inc(v_key_4303_);
                            leanh::lean_dec(v_v_4294_);
                            v___x_4306_ = leanh::lean_box(0);
                            v_isShared_4307_ = v_isSharedCheck_4314_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4315_ = leanh::lean_ctor_get(v_v_4294_, 0);
                        v_isSharedCheck_4325_ = (!leanh::lean_is_exclusive(v_v_4294_)) as u8;
                        if v_isSharedCheck_4325_ == 0 {
                            v___x_4317_ = v_v_4294_;
                            v_isShared_4318_ = v_isSharedCheck_4325_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4315_);
                            leanh::lean_dec(v_v_4294_);
                            v___x_4317_ = leanh::lean_box(0);
                            v_isShared_4318_ = v_isSharedCheck_4325_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4326_, 0, v_x_4281_);
                        leanh::lean_ctor_set(v___x_4326_, 1, v_x_4282_);
                        v___y_4298_ = v___x_4326_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4299_ = lean_array_fset(v_xs_x27_4296_, v_j_4288_, v___y_4298_);
                leanh::lean_dec(v_j_4288_);
                if v_isShared_4293_ == 0 {
                    leanh::lean_ctor_set(v___x_4292_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4292_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4301_;
            }
            4 => {
                v___x_4308_ = l_Lean_instBEqMVarId_beq(v_x_4281_, v_key_4303_);
                if v___x_4308_ == 0 {
                    leanh::lean_del_object(v___x_4306_);
                    v___x_4309_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4303_,
                        v_val_4304_,
                        v_x_4281_,
                        v_x_4282_,
                    );
                    v___x_4310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4310_, 0, v___x_4309_);
                    v___y_4298_ = v___x_4310_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4304_);
                    leanh::lean_dec(v_key_4303_);
                    if v_isShared_4307_ == 0 {
                        leanh::lean_ctor_set(v___x_4306_, 1, v_x_4282_);
                        leanh::lean_ctor_set(v___x_4306_, 0, v_x_4281_);
                        v___x_4312_ = v___x_4306_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4313_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_x_4281_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_x_4282_);
                        v___x_4312_ = v_reuseFailAlloc_4313_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4298_ = v___x_4312_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4319_ = lean_usize_shift_right(v_x_4279_, v___x_4284_);
                v___x_4320_ = lean_usize_add(v_x_4280_, v___x_4285_);
                v___x_4321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_node_4315_, v___x_4319_, v___x_4320_, v_x_4281_, v_x_4282_);
                if v_isShared_4318_ == 0 {
                    leanh::lean_ctor_set(v___x_4317_, 0, v___x_4321_);
                    v___x_4323_ = v___x_4317_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
                    v___x_4323_ = v_reuseFailAlloc_4324_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4298_ = v___x_4323_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4333_ == 0 {
                    v___x_4335_ = v___x_4332_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4349_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_ks_4329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4349_, 1, v_vs_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4349_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4336_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v___x_4335_, v_x_4281_, v_x_4282_);
                v___x_4344_ = 7usize;
                v___x_4345_ = lean_usize_dec_le(v___x_4344_, v_x_4280_);
                if v___x_4345_ == 0 {
                    v___x_4346_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4336_);
                    v___x_4347_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4348_ = lean_nat_dec_lt(v___x_4346_, v___x_4347_);
                    leanh::lean_dec(v___x_4346_);
                    v___y_4338_ = v___x_4348_;
                    state = 10;
                    continue;
                } else {
                    v___y_4338_ = v___x_4345_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4338_ == 0 {
                    v_ks_4339_ = leanh::lean_ctor_get(v_newNode_4336_, 0);
                    leanh::lean_inc_ref(v_ks_4339_);
                    v_vs_4340_ = leanh::lean_ctor_get(v_newNode_4336_, 1);
                    leanh::lean_inc_ref(v_vs_4340_);
                    leanh::lean_dec_ref(v_newNode_4336_);
                    v___x_4341_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4342_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2);
                    v___x_4343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_4280_, v_ks_4339_, v_vs_4340_, v___x_4341_, v___x_4342_);
                    leanh::lean_dec_ref(v_vs_4340_);
                    leanh::lean_dec_ref(v_ks_4339_);
                    return v___x_4343_;
                } else {
                    return v_newNode_4336_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(
    mut v_depth_4351_: usize,
    mut v_keys_4352_: *mut leanh::LeanObject,
    mut v_vals_4353_: *mut leanh::LeanObject,
    mut v_i_4354_: *mut leanh::LeanObject,
    mut v_entries_4355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v_k_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u64 = 0;
    let mut v_h_4361_: usize = 0;
    let mut v___x_4362_: usize = 0;
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: usize = 0;
    let mut v___x_4365_: usize = 0;
    let mut v___x_4366_: usize = 0;
    let mut v_h_4367_: usize = 0;
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4356_ = lean_array_get_size(v_keys_4352_);
                v___x_4357_ = lean_nat_dec_lt(v_i_4354_, v___x_4356_);
                if v___x_4357_ == 0 {
                    leanh::lean_dec(v_i_4354_);
                    return v_entries_4355_;
                } else {
                    v_k_4358_ = lean_array_fget_borrowed(v_keys_4352_, v_i_4354_);
                    v_v_4359_ = lean_array_fget_borrowed(v_vals_4353_, v_i_4354_);
                    v___x_4360_ = l_Lean_instHashableMVarId_hash(v_k_4358_);
                    v_h_4361_ = lean_uint64_to_usize(v___x_4360_);
                    v___x_4362_ = 5usize;
                    v___x_4363_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4364_ = 1usize;
                    v___x_4365_ = lean_usize_sub(v_depth_4351_, v___x_4364_);
                    v___x_4366_ = lean_usize_mul(v___x_4362_, v___x_4365_);
                    v_h_4367_ = lean_usize_shift_right(v_h_4361_, v___x_4366_);
                    v___x_4368_ = lean_nat_add(v_i_4354_, v___x_4363_);
                    leanh::lean_dec(v_i_4354_);
                    leanh::lean_inc(v_v_4359_);
                    leanh::lean_inc(v_k_4358_);
                    v___x_4369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_entries_4355_, v_h_4367_, v_depth_4351_, v_k_4358_, v_v_4359_);
                    v_i_4354_ = v___x_4368_;
                    v_entries_4355_ = v___x_4369_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg___boxed(
    mut v_depth_4371_: *mut leanh::LeanObject,
    mut v_keys_4372_: *mut leanh::LeanObject,
    mut v_vals_4373_: *mut leanh::LeanObject,
    mut v_i_4374_: *mut leanh::LeanObject,
    mut v_entries_4375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4376_: usize = 0;
    let mut v_res_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4376_ = leanh::lean_unbox_usize(v_depth_4371_);
    leanh::lean_dec(v_depth_4371_);
    v_res_4377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_4376_, v_keys_4372_, v_vals_4373_, v_i_4374_, v_entries_4375_);
    leanh::lean_dec_ref(v_vals_4373_);
    leanh::lean_dec_ref(v_keys_4372_);
    return v_res_4377_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_x_4378_: *mut leanh::LeanObject,
    mut v_x_4379_: *mut leanh::LeanObject,
    mut v_x_4380_: *mut leanh::LeanObject,
    mut v_x_4381_: *mut leanh::LeanObject,
    mut v_x_4382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4896__boxed_4383_: usize = 0;
    let mut v_x_4897__boxed_4384_: usize = 0;
    let mut v_res_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4896__boxed_4383_ = leanh::lean_unbox_usize(v_x_4379_);
    leanh::lean_dec(v_x_4379_);
    v_x_4897__boxed_4384_ = leanh::lean_unbox_usize(v_x_4380_);
    leanh::lean_dec(v_x_4380_);
    v_res_4385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_4378_, v_x_4896__boxed_4383_, v_x_4897__boxed_4384_, v_x_4381_, v_x_4382_);
    return v_res_4385_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(
    mut v_x_4386_: *mut leanh::LeanObject,
    mut v_x_4387_: *mut leanh::LeanObject,
    mut v_x_4388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4389_: u64 = 0;
    let mut v___x_4390_: usize = 0;
    let mut v___x_4391_: usize = 0;
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_instHashableMVarId_hash(v_x_4387_);
    v___x_4390_ = lean_uint64_to_usize(v___x_4389_);
    v___x_4391_ = 1usize;
    v___x_4392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_4386_, v___x_4390_, v___x_4391_, v_x_4387_, v_x_4388_);
    return v___x_4392_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(
    mut v_mvarId_4393_: *mut leanh::LeanObject,
    mut v_val_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4405_: u8 = 0;
    let mut v_depth_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4429_: u8 = 0;
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4397_ = lean_st_ref_take(v___y_4395_);
                v_mctx_4398_ = leanh::lean_ctor_get(v___x_4397_, 0);
                v_cache_4399_ = leanh::lean_ctor_get(v___x_4397_, 1);
                v_zetaDeltaFVarIds_4400_ = leanh::lean_ctor_get(v___x_4397_, 2);
                v_postponed_4401_ = leanh::lean_ctor_get(v___x_4397_, 3);
                v_diag_4402_ = leanh::lean_ctor_get(v___x_4397_, 4);
                v_isSharedCheck_4430_ = (!leanh::lean_is_exclusive(v___x_4397_)) as u8;
                if v_isSharedCheck_4430_ == 0 {
                    v___x_4404_ = v___x_4397_;
                    v_isShared_4405_ = v_isSharedCheck_4430_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4402_);
                    leanh::lean_inc(v_postponed_4401_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4400_);
                    leanh::lean_inc(v_cache_4399_);
                    leanh::lean_inc(v_mctx_4398_);
                    leanh::lean_dec(v___x_4397_);
                    v___x_4404_ = leanh::lean_box(0);
                    v_isShared_4405_ = v_isSharedCheck_4430_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4406_ = leanh::lean_ctor_get(v_mctx_4398_, 0);
                v_levelAssignDepth_4407_ = leanh::lean_ctor_get(v_mctx_4398_, 1);
                v_lmvarCounter_4408_ = leanh::lean_ctor_get(v_mctx_4398_, 2);
                v_mvarCounter_4409_ = leanh::lean_ctor_get(v_mctx_4398_, 3);
                v_lDecls_4410_ = leanh::lean_ctor_get(v_mctx_4398_, 4);
                v_decls_4411_ = leanh::lean_ctor_get(v_mctx_4398_, 5);
                v_userNames_4412_ = leanh::lean_ctor_get(v_mctx_4398_, 6);
                v_lAssignment_4413_ = leanh::lean_ctor_get(v_mctx_4398_, 7);
                v_eAssignment_4414_ = leanh::lean_ctor_get(v_mctx_4398_, 8);
                v_dAssignment_4415_ = leanh::lean_ctor_get(v_mctx_4398_, 9);
                v_isSharedCheck_4429_ = (!leanh::lean_is_exclusive(v_mctx_4398_)) as u8;
                if v_isSharedCheck_4429_ == 0 {
                    v___x_4417_ = v_mctx_4398_;
                    v_isShared_4418_ = v_isSharedCheck_4429_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_4415_);
                    leanh::lean_inc(v_eAssignment_4414_);
                    leanh::lean_inc(v_lAssignment_4413_);
                    leanh::lean_inc(v_userNames_4412_);
                    leanh::lean_inc(v_decls_4411_);
                    leanh::lean_inc(v_lDecls_4410_);
                    leanh::lean_inc(v_mvarCounter_4409_);
                    leanh::lean_inc(v_lmvarCounter_4408_);
                    leanh::lean_inc(v_levelAssignDepth_4407_);
                    leanh::lean_inc(v_depth_4406_);
                    leanh::lean_dec(v_mctx_4398_);
                    v___x_4417_ = leanh::lean_box(0);
                    v_isShared_4418_ = v_isSharedCheck_4429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4419_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_4414_, v_mvarId_4393_, v_val_4394_);
                if v_isShared_4418_ == 0 {
                    leanh::lean_ctor_set(v___x_4417_, 8, v___x_4419_);
                    v___x_4421_ = v___x_4417_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4428_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_depth_4406_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4428_,
                        1,
                        v_levelAssignDepth_4407_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_lmvarCounter_4408_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 3, v_mvarCounter_4409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 4, v_lDecls_4410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 5, v_decls_4411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 6, v_userNames_4412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 7, v_lAssignment_4413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 8, v___x_4419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 9, v_dAssignment_4415_);
                    v___x_4421_ = v_reuseFailAlloc_4428_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4405_ == 0 {
                    leanh::lean_ctor_set(v___x_4404_, 0, v___x_4421_);
                    v___x_4423_ = v___x_4404_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4427_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_cache_4399_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4427_,
                        2,
                        v_zetaDeltaFVarIds_4400_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 3, v_postponed_4401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 4, v_diag_4402_);
                    v___x_4423_ = v_reuseFailAlloc_4427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4424_ = lean_st_ref_set(v___y_4395_, v___x_4423_);
                v___x_4425_ = leanh::lean_box(0);
                v___x_4426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4426_, 0, v___x_4425_);
                return v___x_4426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(
    mut v_mvarId_4431_: *mut leanh::LeanObject,
    mut v_val_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(
        v_mvarId_4431_,
        v_val_4432_,
        v___y_4433_,
    );
    leanh::lean_dec(v___y_4433_);
    return v_res_4435_;
}
pub unsafe fn l_Lean_MVarId_instantiateGoalMVars(
    mut v_mvarId_4436_: *mut leanh::LeanObject,
    mut v_a_4437_: *mut leanh::LeanObject,
    mut v_a_4438_: *mut leanh::LeanObject,
    mut v_a_4439_: *mut leanh::LeanObject,
    mut v_a_4440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: u8 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_unused_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_a_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_a_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut v_a_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4442_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                leanh::lean_inc(v_mvarId_4436_);
                v___x_4443_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4436_,
                    v___x_4442_,
                    v_a_4437_,
                    v_a_4438_,
                    v_a_4439_,
                    v_a_4440_,
                );
                if leanh::lean_obj_tag(v___x_4443_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4443_, 1);
                    leanh::lean_inc(v_mvarId_4436_);
                    v___x_4444_ = l_Lean_MVarId_getDecl(
                        v_mvarId_4436_,
                        v_a_4437_,
                        v_a_4438_,
                        v_a_4439_,
                        v_a_4440_,
                    );
                    if leanh::lean_obj_tag(v___x_4444_) == 0 {
                        v_a_4445_ = leanh::lean_ctor_get(v___x_4444_, 0);
                        leanh::lean_inc(v_a_4445_);
                        leanh::lean_dec_ref_known(v___x_4444_, 1);
                        v_userName_4446_ = leanh::lean_ctor_get(v_a_4445_, 0);
                        leanh::lean_inc(v_userName_4446_);
                        v_lctx_4447_ = leanh::lean_ctor_get(v_a_4445_, 1);
                        leanh::lean_inc_ref(v_lctx_4447_);
                        v_type_4448_ = leanh::lean_ctor_get(v_a_4445_, 2);
                        leanh::lean_inc_ref(v_type_4448_);
                        v_localInstances_4449_ = leanh::lean_ctor_get(v_a_4445_, 4);
                        leanh::lean_inc_ref(v_localInstances_4449_);
                        leanh::lean_dec(v_a_4445_);
                        v___x_4450_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_4447_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_);
                        if leanh::lean_obj_tag(v___x_4450_) == 0 {
                            v_a_4451_ = leanh::lean_ctor_get(v___x_4450_, 0);
                            leanh::lean_inc(v_a_4451_);
                            leanh::lean_dec_ref_known(v___x_4450_, 1);
                            v___x_4452_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_4448_, v_a_4438_);
                            v_a_4453_ = leanh::lean_ctor_get(v___x_4452_, 0);
                            leanh::lean_inc(v_a_4453_);
                            leanh::lean_dec_ref(v___x_4452_);
                            v___x_4454_ = 2;
                            v___x_4455_ = leanh::lean_unsigned_to_nat(0);
                            v___x_4456_ = l_Lean_Meta_mkFreshExprMVarAt(
                                v_a_4451_,
                                v_localInstances_4449_,
                                v_a_4453_,
                                v___x_4454_,
                                v_userName_4446_,
                                v___x_4455_,
                                v_a_4437_,
                                v_a_4438_,
                                v_a_4439_,
                                v_a_4440_,
                            );
                            if leanh::lean_obj_tag(v___x_4456_) == 0 {
                                v_a_4457_ = leanh::lean_ctor_get(v___x_4456_, 0);
                                leanh::lean_inc_n(v_a_4457_, 2);
                                leanh::lean_dec_ref_known(v___x_4456_, 1);
                                v___x_4458_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_4436_, v_a_4457_, v_a_4438_);
                                v_isSharedCheck_4466_ =
                                    (!leanh::lean_is_exclusive(v___x_4458_)) as u8;
                                if v_isSharedCheck_4466_ == 0 {
                                    v_unused_4467_ = leanh::lean_ctor_get(v___x_4458_, 0);
                                    leanh::lean_dec(v_unused_4467_);
                                    v___x_4460_ = v___x_4458_;
                                    v_isShared_4461_ = v_isSharedCheck_4466_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_4458_);
                                    v___x_4460_ = leanh::lean_box(0);
                                    v_isShared_4461_ = v_isSharedCheck_4466_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_mvarId_4436_);
                                v_a_4468_ = leanh::lean_ctor_get(v___x_4456_, 0);
                                v_isSharedCheck_4475_ =
                                    (!leanh::lean_is_exclusive(v___x_4456_)) as u8;
                                if v_isSharedCheck_4475_ == 0 {
                                    v___x_4470_ = v___x_4456_;
                                    v_isShared_4471_ = v_isSharedCheck_4475_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4468_);
                                    leanh::lean_dec(v___x_4456_);
                                    v___x_4470_ = leanh::lean_box(0);
                                    v_isShared_4471_ = v_isSharedCheck_4475_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_localInstances_4449_);
                            leanh::lean_dec_ref(v_type_4448_);
                            leanh::lean_dec(v_userName_4446_);
                            leanh::lean_dec(v_mvarId_4436_);
                            v_a_4476_ = leanh::lean_ctor_get(v___x_4450_, 0);
                            v_isSharedCheck_4483_ =
                                (!leanh::lean_is_exclusive(v___x_4450_)) as u8;
                            if v_isSharedCheck_4483_ == 0 {
                                v___x_4478_ = v___x_4450_;
                                v_isShared_4479_ = v_isSharedCheck_4483_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4476_);
                                leanh::lean_dec(v___x_4450_);
                                v___x_4478_ = leanh::lean_box(0);
                                v_isShared_4479_ = v_isSharedCheck_4483_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_4436_);
                        v_a_4484_ = leanh::lean_ctor_get(v___x_4444_, 0);
                        v_isSharedCheck_4491_ =
                            (!leanh::lean_is_exclusive(v___x_4444_)) as u8;
                        if v_isSharedCheck_4491_ == 0 {
                            v___x_4486_ = v___x_4444_;
                            v_isShared_4487_ = v_isSharedCheck_4491_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4484_);
                            leanh::lean_dec(v___x_4444_);
                            v___x_4486_ = leanh::lean_box(0);
                            v_isShared_4487_ = v_isSharedCheck_4491_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_4436_);
                    v_a_4492_ = leanh::lean_ctor_get(v___x_4443_, 0);
                    v_isSharedCheck_4499_ = (!leanh::lean_is_exclusive(v___x_4443_)) as u8;
                    if v_isSharedCheck_4499_ == 0 {
                        v___x_4494_ = v___x_4443_;
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4492_);
                        leanh::lean_dec(v___x_4443_);
                        v___x_4494_ = leanh::lean_box(0);
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4462_ = l_Lean_Expr_mvarId_x21(v_a_4457_);
                leanh::lean_dec(v_a_4457_);
                if v_isShared_4461_ == 0 {
                    leanh::lean_ctor_set(v___x_4460_, 0, v___x_4462_);
                    v___x_4464_ = v___x_4460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4464_;
            }
            3 => {
                if v_isShared_4471_ == 0 {
                    v___x_4473_ = v___x_4470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
                    v___x_4473_ = v_reuseFailAlloc_4474_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4473_;
            }
            5 => {
                if v_isShared_4479_ == 0 {
                    v___x_4481_ = v___x_4478_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
                    v___x_4481_ = v_reuseFailAlloc_4482_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4481_;
            }
            7 => {
                if v_isShared_4487_ == 0 {
                    v___x_4489_ = v___x_4486_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4490_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
                    v___x_4489_ = v_reuseFailAlloc_4490_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4489_;
            }
            9 => {
                if v_isShared_4495_ == 0 {
                    v___x_4497_ = v___x_4494_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4498_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
                    v___x_4497_ = v_reuseFailAlloc_4498_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4497_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_instantiateGoalMVars___boxed(
    mut v_mvarId_4500_: *mut leanh::LeanObject,
    mut v_a_4501_: *mut leanh::LeanObject,
    mut v_a_4502_: *mut leanh::LeanObject,
    mut v_a_4503_: *mut leanh::LeanObject,
    mut v_a_4504_: *mut leanh::LeanObject,
    mut v_a_4505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4506_ = l_Lean_MVarId_instantiateGoalMVars(
        v_mvarId_4500_,
        v_a_4501_,
        v_a_4502_,
        v_a_4503_,
        v_a_4504_,
    );
    leanh::lean_dec(v_a_4504_);
    leanh::lean_dec_ref(v_a_4503_);
    leanh::lean_dec(v_a_4502_);
    leanh::lean_dec_ref(v_a_4501_);
    return v_res_4506_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(
    mut v_mvarId_4507_: *mut leanh::LeanObject,
    mut v_val_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4514_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(
        v_mvarId_4507_,
        v_val_4508_,
        v___y_4510_,
    );
    return v___x_4514_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(
    mut v_mvarId_4515_: *mut leanh::LeanObject,
    mut v_val_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
    mut v___y_4520_: *mut leanh::LeanObject,
    mut v___y_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4522_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(
        v_mvarId_4515_,
        v_val_4516_,
        v___y_4517_,
        v___y_4518_,
        v___y_4519_,
        v___y_4520_,
    );
    leanh::lean_dec(v___y_4520_);
    leanh::lean_dec_ref(v___y_4519_);
    leanh::lean_dec(v___y_4518_);
    leanh::lean_dec_ref(v___y_4517_);
    return v_res_4522_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(
    mut v_00_u03b4_4523_: *mut leanh::LeanObject,
    mut v_t_4524_: *mut leanh::LeanObject,
    mut v_k_4525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_4524_, v_k_4525_);
    return v___x_4526_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(
    mut v_00_u03b4_4527_: *mut leanh::LeanObject,
    mut v_t_4528_: *mut leanh::LeanObject,
    mut v_k_4529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_4527_, v_t_4528_, v_k_4529_);
    leanh::lean_dec(v_k_4529_);
    leanh::lean_dec(v_t_4528_);
    return v_res_4530_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(
    mut v_00_u03b2_4531_: *mut leanh::LeanObject,
    mut v_x_4532_: *mut leanh::LeanObject,
    mut v_x_4533_: *mut leanh::LeanObject,
    mut v_x_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_4532_, v_x_4533_, v_x_4534_);
    return v___x_4535_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(
    mut v_00_u03b2_4536_: *mut leanh::LeanObject,
    mut v_x_4537_: *mut leanh::LeanObject,
    mut v_x_4538_: usize,
    mut v_x_4539_: usize,
    mut v_x_4540_: *mut leanh::LeanObject,
    mut v_x_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_4537_, v_x_4538_, v_x_4539_, v_x_4540_, v_x_4541_);
    return v___x_4542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b2_4543_: *mut leanh::LeanObject,
    mut v_x_4544_: *mut leanh::LeanObject,
    mut v_x_4545_: *mut leanh::LeanObject,
    mut v_x_4546_: *mut leanh::LeanObject,
    mut v_x_4547_: *mut leanh::LeanObject,
    mut v_x_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5262__boxed_4549_: usize = 0;
    let mut v_x_5263__boxed_4550_: usize = 0;
    let mut v_res_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5262__boxed_4549_ = leanh::lean_unbox_usize(v_x_4545_);
    leanh::lean_dec(v_x_4545_);
    v_x_5263__boxed_4550_ = leanh::lean_unbox_usize(v_x_4546_);
    leanh::lean_dec(v_x_4546_);
    v_res_4551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_4543_, v_x_4544_, v_x_5262__boxed_4549_, v_x_5263__boxed_4550_, v_x_4547_, v_x_4548_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(
    mut v_00_u03b2_4552_: *mut leanh::LeanObject,
    mut v_n_4553_: *mut leanh::LeanObject,
    mut v_k_4554_: *mut leanh::LeanObject,
    mut v_v_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_4553_, v_k_4554_, v_v_4555_);
    return v___x_4556_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(
    mut v_00_u03b2_4557_: *mut leanh::LeanObject,
    mut v_depth_4558_: usize,
    mut v_keys_4559_: *mut leanh::LeanObject,
    mut v_vals_4560_: *mut leanh::LeanObject,
    mut v_heq_4561_: *mut leanh::LeanObject,
    mut v_i_4562_: *mut leanh::LeanObject,
    mut v_entries_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_4558_, v_keys_4559_, v_vals_4560_, v_i_4562_, v_entries_4563_);
    return v___x_4564_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(
    mut v_00_u03b2_4565_: *mut leanh::LeanObject,
    mut v_depth_4566_: *mut leanh::LeanObject,
    mut v_keys_4567_: *mut leanh::LeanObject,
    mut v_vals_4568_: *mut leanh::LeanObject,
    mut v_heq_4569_: *mut leanh::LeanObject,
    mut v_i_4570_: *mut leanh::LeanObject,
    mut v_entries_4571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4572_: usize = 0;
    let mut v_res_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4572_ = leanh::lean_unbox_usize(v_depth_4566_);
    leanh::lean_dec(v_depth_4566_);
    v_res_4573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_4565_, v_depth_boxed_4572_, v_keys_4567_, v_vals_4568_, v_heq_4569_, v_i_4570_, v_entries_4571_);
    leanh::lean_dec_ref(v_vals_4568_);
    leanh::lean_dec_ref(v_keys_4567_);
    return v_res_4573_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(
    mut v_00_u03b2_4574_: *mut leanh::LeanObject,
    mut v_x_4575_: *mut leanh::LeanObject,
    mut v_x_4576_: *mut leanh::LeanObject,
    mut v_x_4577_: *mut leanh::LeanObject,
    mut v_x_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4579_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_4575_, v_x_4576_, v_x_4577_, v_x_4578_);
    return v___x_4579_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(
    mut v_k_4580_: *mut leanh::LeanObject,
    mut v_b_4581_: *mut leanh::LeanObject,
    mut v_c_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
    mut v___y_4586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4586_);
    leanh::lean_inc_ref(v___y_4585_);
    leanh::lean_inc(v___y_4584_);
    leanh::lean_inc_ref(v___y_4583_);
    v___x_4588_ = leanh::lean_apply_7(
        v_k_4580_,
        v_b_4581_,
        v_c_4582_,
        v___y_4583_,
        v___y_4584_,
        v___y_4585_,
        v___y_4586_,
        leanh::lean_box(0),
    );
    return v___x_4588_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(
    mut v_k_4589_: *mut leanh::LeanObject,
    mut v_b_4590_: *mut leanh::LeanObject,
    mut v_c_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
    mut v___y_4593_: *mut leanh::LeanObject,
    mut v___y_4594_: *mut leanh::LeanObject,
    mut v___y_4595_: *mut leanh::LeanObject,
    mut v___y_4596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4597_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(
            v_k_4589_,
            v_b_4590_,
            v_c_4591_,
            v___y_4592_,
            v___y_4593_,
            v___y_4594_,
            v___y_4595_,
        );
    leanh::lean_dec(v___y_4595_);
    leanh::lean_dec_ref(v___y_4594_);
    leanh::lean_dec(v___y_4593_);
    leanh::lean_dec_ref(v___y_4592_);
    return v_res_4597_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(
    mut v_e_4598_: *mut leanh::LeanObject,
    mut v_k_4599_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4600_: u8,
    mut v___y_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
    mut v___y_4603_: *mut leanh::LeanObject,
    mut v___y_4604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: u8 = 0;
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4606_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_4606_, 0, v_k_4599_);
                v___x_4607_ = 1;
                v___x_4608_ = 0;
                v___x_4609_ = leanh::lean_box(0);
                v___x_4610_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_4598_,
                    v___x_4607_,
                    v___x_4608_,
                    v___x_4607_,
                    v___x_4608_,
                    v___x_4609_,
                    v___f_4606_,
                    v_cleanupAnnotations_4600_,
                    v___y_4601_,
                    v___y_4602_,
                    v___y_4603_,
                    v___y_4604_,
                );
                if leanh::lean_obj_tag(v___x_4610_) == 0 {
                    v_a_4611_ = leanh::lean_ctor_get(v___x_4610_, 0);
                    v_isSharedCheck_4618_ = (!leanh::lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4613_ = v___x_4610_;
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4611_);
                        leanh::lean_dec(v___x_4610_);
                        v___x_4613_ = leanh::lean_box(0);
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4619_ = leanh::lean_ctor_get(v___x_4610_, 0);
                    v_isSharedCheck_4626_ = (!leanh::lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4610_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4619_);
                        leanh::lean_dec(v___x_4610_);
                        v___x_4621_ = leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4616_;
            }
            3 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(
    mut v_e_4627_: *mut leanh::LeanObject,
    mut v_k_4628_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
    mut v___y_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4635_: u8 = 0;
    let mut v_res_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4635_ = (leanh::lean_unbox(v_cleanupAnnotations_4629_) as u8);
    v_res_4636_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(
        v_e_4627_,
        v_k_4628_,
        v_cleanupAnnotations_boxed_4635_,
        v___y_4630_,
        v___y_4631_,
        v___y_4632_,
        v___y_4633_,
    );
    leanh::lean_dec(v___y_4633_);
    leanh::lean_dec_ref(v___y_4632_);
    leanh::lean_dec(v___y_4631_);
    leanh::lean_dec_ref(v___y_4630_);
    return v_res_4636_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(
    mut v_00_u03b1_4637_: *mut leanh::LeanObject,
    mut v_e_4638_: *mut leanh::LeanObject,
    mut v_k_4639_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4640_: u8,
    mut v___y_4641_: *mut leanh::LeanObject,
    mut v___y_4642_: *mut leanh::LeanObject,
    mut v___y_4643_: *mut leanh::LeanObject,
    mut v___y_4644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4646_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(
        v_e_4638_,
        v_k_4639_,
        v_cleanupAnnotations_4640_,
        v___y_4641_,
        v___y_4642_,
        v___y_4643_,
        v___y_4644_,
    );
    return v___x_4646_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(
    mut v_00_u03b1_4647_: *mut leanh::LeanObject,
    mut v_e_4648_: *mut leanh::LeanObject,
    mut v_k_4649_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
    mut v___y_4652_: *mut leanh::LeanObject,
    mut v___y_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4656_: u8 = 0;
    let mut v_res_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4656_ = (leanh::lean_unbox(v_cleanupAnnotations_4650_) as u8);
    v_res_4657_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(
        v_00_u03b1_4647_,
        v_e_4648_,
        v_k_4649_,
        v_cleanupAnnotations_boxed_4656_,
        v___y_4651_,
        v___y_4652_,
        v___y_4653_,
        v___y_4654_,
    );
    leanh::lean_dec(v___y_4654_);
    leanh::lean_dec_ref(v___y_4653_);
    leanh::lean_dec(v___y_4652_);
    leanh::lean_dec_ref(v___y_4651_);
    return v_res_4657_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
    mut v_mvarId_4658_: *mut leanh::LeanObject,
    mut v_x_4659_: *mut leanh::LeanObject,
    mut v___y_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
    mut v___y_4662_: *mut leanh::LeanObject,
    mut v___y_4663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4669_: u8 = 0;
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_a_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_4658_,
                    v_x_4659_,
                    v___y_4660_,
                    v___y_4661_,
                    v___y_4662_,
                    v___y_4663_,
                );
                if leanh::lean_obj_tag(v___x_4665_) == 0 {
                    v_a_4666_ = leanh::lean_ctor_get(v___x_4665_, 0);
                    v_isSharedCheck_4673_ = (!leanh::lean_is_exclusive(v___x_4665_)) as u8;
                    if v_isSharedCheck_4673_ == 0 {
                        v___x_4668_ = v___x_4665_;
                        v_isShared_4669_ = v_isSharedCheck_4673_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4666_);
                        leanh::lean_dec(v___x_4665_);
                        v___x_4668_ = leanh::lean_box(0);
                        v_isShared_4669_ = v_isSharedCheck_4673_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4674_ = leanh::lean_ctor_get(v___x_4665_, 0);
                    v_isSharedCheck_4681_ = (!leanh::lean_is_exclusive(v___x_4665_)) as u8;
                    if v_isSharedCheck_4681_ == 0 {
                        v___x_4676_ = v___x_4665_;
                        v_isShared_4677_ = v_isSharedCheck_4681_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4674_);
                        leanh::lean_dec(v___x_4665_);
                        v___x_4676_ = leanh::lean_box(0);
                        v_isShared_4677_ = v_isSharedCheck_4681_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4669_ == 0 {
                    v___x_4671_ = v___x_4668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
                    v___x_4671_ = v_reuseFailAlloc_4672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4671_;
            }
            3 => {
                if v_isShared_4677_ == 0 {
                    v___x_4679_ = v___x_4676_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
                    v___x_4679_ = v_reuseFailAlloc_4680_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(
    mut v_mvarId_4682_: *mut leanh::LeanObject,
    mut v_x_4683_: *mut leanh::LeanObject,
    mut v___y_4684_: *mut leanh::LeanObject,
    mut v___y_4685_: *mut leanh::LeanObject,
    mut v___y_4686_: *mut leanh::LeanObject,
    mut v___y_4687_: *mut leanh::LeanObject,
    mut v___y_4688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4689_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
        v_mvarId_4682_,
        v_x_4683_,
        v___y_4684_,
        v___y_4685_,
        v___y_4686_,
        v___y_4687_,
    );
    leanh::lean_dec(v___y_4687_);
    leanh::lean_dec_ref(v___y_4686_);
    leanh::lean_dec(v___y_4685_);
    leanh::lean_dec_ref(v___y_4684_);
    return v_res_4689_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(
    mut v_00_u03b1_4690_: *mut leanh::LeanObject,
    mut v_mvarId_4691_: *mut leanh::LeanObject,
    mut v_x_4692_: *mut leanh::LeanObject,
    mut v___y_4693_: *mut leanh::LeanObject,
    mut v___y_4694_: *mut leanh::LeanObject,
    mut v___y_4695_: *mut leanh::LeanObject,
    mut v___y_4696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
        v_mvarId_4691_,
        v_x_4692_,
        v___y_4693_,
        v___y_4694_,
        v___y_4695_,
        v___y_4696_,
    );
    return v___x_4698_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(
    mut v_00_u03b1_4699_: *mut leanh::LeanObject,
    mut v_mvarId_4700_: *mut leanh::LeanObject,
    mut v_x_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
    mut v___y_4704_: *mut leanh::LeanObject,
    mut v___y_4705_: *mut leanh::LeanObject,
    mut v___y_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(
        v_00_u03b1_4699_,
        v_mvarId_4700_,
        v_x_4701_,
        v___y_4702_,
        v___y_4703_,
        v___y_4704_,
        v___y_4705_,
    );
    leanh::lean_dec(v___y_4705_);
    leanh::lean_dec_ref(v___y_4704_);
    leanh::lean_dec(v___y_4703_);
    leanh::lean_dec_ref(v___y_4702_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars___lam__0(
    mut v___x_4708_: u8,
    mut v___x_4709_: u8,
    mut v_xs_4710_: *mut leanh::LeanObject,
    mut v_body_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
    mut v___y_4714_: *mut leanh::LeanObject,
    mut v___y_4715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ = 1;
    v___x_4718_ = l_Lean_Meta_mkForallFVars(
        v_xs_4710_,
        v_body_4711_,
        v___x_4708_,
        v___x_4709_,
        v___x_4709_,
        v___x_4717_,
        v___y_4712_,
        v___y_4713_,
        v___y_4714_,
        v___y_4715_,
    );
    return v___x_4718_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars___lam__0___boxed(
    mut v___x_4719_: *mut leanh::LeanObject,
    mut v___x_4720_: *mut leanh::LeanObject,
    mut v_xs_4721_: *mut leanh::LeanObject,
    mut v_body_4722_: *mut leanh::LeanObject,
    mut v___y_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1951__boxed_4728_: u8 = 0;
    let mut v___x_1952__boxed_4729_: u8 = 0;
    let mut v_res_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1951__boxed_4728_ = (leanh::lean_unbox(v___x_4719_) as u8);
    v___x_1952__boxed_4729_ = (leanh::lean_unbox(v___x_4720_) as u8);
    v_res_4730_ = l_Lean_MVarId_abstractMVars___lam__0(
        v___x_1951__boxed_4728_,
        v___x_1952__boxed_4729_,
        v_xs_4721_,
        v_body_4722_,
        v___y_4723_,
        v___y_4724_,
        v___y_4725_,
        v___y_4726_,
    );
    leanh::lean_dec(v___y_4726_);
    leanh::lean_dec_ref(v___y_4725_);
    leanh::lean_dec(v___y_4724_);
    leanh::lean_dec_ref(v___y_4723_);
    leanh::lean_dec_ref(v_xs_4721_);
    return v_res_4730_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars___lam__1(
    mut v_a_4731_: *mut leanh::LeanObject,
    mut v___x_4732_: u8,
    mut v___f_4733_: *mut leanh::LeanObject,
    mut v_mvarId_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v_unused_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut v_a_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4772_: u8 = 0;
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4776_: u8 = 0;
    let mut v_a_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4784_: u8 = 0;
    let mut v_a_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4788_: u8 = 0;
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4740_ = l_Lean_Meta_abstractMVars(
                    v_a_4731_,
                    v___x_4732_,
                    v___y_4735_,
                    v___y_4736_,
                    v___y_4737_,
                    v___y_4738_,
                );
                if leanh::lean_obj_tag(v___x_4740_) == 0 {
                    v_a_4741_ = leanh::lean_ctor_get(v___x_4740_, 0);
                    leanh::lean_inc(v_a_4741_);
                    leanh::lean_dec_ref_known(v___x_4740_, 1);
                    v_mvars_4742_ = leanh::lean_ctor_get(v_a_4741_, 1);
                    leanh::lean_inc_ref(v_mvars_4742_);
                    v_expr_4743_ = leanh::lean_ctor_get(v_a_4741_, 2);
                    leanh::lean_inc_ref(v_expr_4743_);
                    leanh::lean_dec(v_a_4741_);
                    v___x_4744_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_4743_, v___f_4733_, v___x_4732_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
                    if leanh::lean_obj_tag(v___x_4744_) == 0 {
                        v_a_4745_ = leanh::lean_ctor_get(v___x_4744_, 0);
                        leanh::lean_inc(v_a_4745_);
                        leanh::lean_dec_ref_known(v___x_4744_, 1);
                        leanh::lean_inc(v_mvarId_4734_);
                        v___x_4746_ = l_Lean_MVarId_getTag(
                            v_mvarId_4734_,
                            v___y_4735_,
                            v___y_4736_,
                            v___y_4737_,
                            v___y_4738_,
                        );
                        if leanh::lean_obj_tag(v___x_4746_) == 0 {
                            v_a_4747_ = leanh::lean_ctor_get(v___x_4746_, 0);
                            leanh::lean_inc(v_a_4747_);
                            leanh::lean_dec_ref_known(v___x_4746_, 1);
                            v___x_4748_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_4745_,
                                v_a_4747_,
                                v___y_4735_,
                                v___y_4736_,
                                v___y_4737_,
                                v___y_4738_,
                            );
                            if leanh::lean_obj_tag(v___x_4748_) == 0 {
                                v_a_4749_ = leanh::lean_ctor_get(v___x_4748_, 0);
                                leanh::lean_inc_n(v_a_4749_, 2);
                                leanh::lean_dec_ref_known(v___x_4748_, 1);
                                v___x_4750_ = l_Lean_mkAppN(v_a_4749_, v_mvars_4742_);
                                leanh::lean_dec_ref(v_mvars_4742_);
                                v___x_4751_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_4734_, v___x_4750_, v___y_4736_);
                                v_isSharedCheck_4759_ =
                                    (!leanh::lean_is_exclusive(v___x_4751_)) as u8;
                                if v_isSharedCheck_4759_ == 0 {
                                    v_unused_4760_ = leanh::lean_ctor_get(v___x_4751_, 0);
                                    leanh::lean_dec(v_unused_4760_);
                                    v___x_4753_ = v___x_4751_;
                                    v_isShared_4754_ = v_isSharedCheck_4759_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_4751_);
                                    v___x_4753_ = leanh::lean_box(0);
                                    v_isShared_4754_ = v_isSharedCheck_4759_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_mvars_4742_);
                                leanh::lean_dec(v_mvarId_4734_);
                                v_a_4761_ = leanh::lean_ctor_get(v___x_4748_, 0);
                                v_isSharedCheck_4768_ =
                                    (!leanh::lean_is_exclusive(v___x_4748_)) as u8;
                                if v_isSharedCheck_4768_ == 0 {
                                    v___x_4763_ = v___x_4748_;
                                    v_isShared_4764_ = v_isSharedCheck_4768_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4761_);
                                    leanh::lean_dec(v___x_4748_);
                                    v___x_4763_ = leanh::lean_box(0);
                                    v_isShared_4764_ = v_isSharedCheck_4768_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4745_);
                            leanh::lean_dec_ref(v_mvars_4742_);
                            leanh::lean_dec(v_mvarId_4734_);
                            v_a_4769_ = leanh::lean_ctor_get(v___x_4746_, 0);
                            v_isSharedCheck_4776_ =
                                (!leanh::lean_is_exclusive(v___x_4746_)) as u8;
                            if v_isSharedCheck_4776_ == 0 {
                                v___x_4771_ = v___x_4746_;
                                v_isShared_4772_ = v_isSharedCheck_4776_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4769_);
                                leanh::lean_dec(v___x_4746_);
                                v___x_4771_ = leanh::lean_box(0);
                                v_isShared_4772_ = v_isSharedCheck_4776_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_mvars_4742_);
                        leanh::lean_dec(v_mvarId_4734_);
                        v_a_4777_ = leanh::lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4784_ =
                            (!leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4784_ == 0 {
                            v___x_4779_ = v___x_4744_;
                            v_isShared_4780_ = v_isSharedCheck_4784_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4777_);
                            leanh::lean_dec(v___x_4744_);
                            v___x_4779_ = leanh::lean_box(0);
                            v_isShared_4780_ = v_isSharedCheck_4784_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_4734_);
                    leanh::lean_dec_ref(v___f_4733_);
                    v_a_4785_ = leanh::lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4792_ = (!leanh::lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4792_ == 0 {
                        v___x_4787_ = v___x_4740_;
                        v_isShared_4788_ = v_isSharedCheck_4792_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4785_);
                        leanh::lean_dec(v___x_4740_);
                        v___x_4787_ = leanh::lean_box(0);
                        v_isShared_4788_ = v_isSharedCheck_4792_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4755_ = l_Lean_Expr_mvarId_x21(v_a_4749_);
                leanh::lean_dec(v_a_4749_);
                if v_isShared_4754_ == 0 {
                    leanh::lean_ctor_set(v___x_4753_, 0, v___x_4755_);
                    v___x_4757_ = v___x_4753_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
                    v___x_4757_ = v_reuseFailAlloc_4758_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4757_;
            }
            3 => {
                if v_isShared_4764_ == 0 {
                    v___x_4766_ = v___x_4763_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
                    v___x_4766_ = v_reuseFailAlloc_4767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4766_;
            }
            5 => {
                if v_isShared_4772_ == 0 {
                    v___x_4774_ = v___x_4771_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
                    v___x_4774_ = v_reuseFailAlloc_4775_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4774_;
            }
            7 => {
                if v_isShared_4780_ == 0 {
                    v___x_4782_ = v___x_4779_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
                    v___x_4782_ = v_reuseFailAlloc_4783_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4782_;
            }
            9 => {
                if v_isShared_4788_ == 0 {
                    v___x_4790_ = v___x_4787_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4791_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
                    v___x_4790_ = v_reuseFailAlloc_4791_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_abstractMVars___lam__1___boxed(
    mut v_a_4793_: *mut leanh::LeanObject,
    mut v___x_4794_: *mut leanh::LeanObject,
    mut v___f_4795_: *mut leanh::LeanObject,
    mut v_mvarId_4796_: *mut leanh::LeanObject,
    mut v___y_4797_: *mut leanh::LeanObject,
    mut v___y_4798_: *mut leanh::LeanObject,
    mut v___y_4799_: *mut leanh::LeanObject,
    mut v___y_4800_: *mut leanh::LeanObject,
    mut v___y_4801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1977__boxed_4802_: u8 = 0;
    let mut v_res_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977__boxed_4802_ = (leanh::lean_unbox(v___x_4794_) as u8);
    v_res_4803_ = l_Lean_MVarId_abstractMVars___lam__1(
        v_a_4793_,
        v___x_1977__boxed_4802_,
        v___f_4795_,
        v_mvarId_4796_,
        v___y_4797_,
        v___y_4798_,
        v___y_4799_,
        v___y_4800_,
    );
    leanh::lean_dec(v___y_4800_);
    leanh::lean_dec_ref(v___y_4799_);
    leanh::lean_dec(v___y_4798_);
    leanh::lean_dec_ref(v___y_4797_);
    return v_res_4803_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars(
    mut v_mvarId_4804_: *mut leanh::LeanObject,
    mut v_a_4805_: *mut leanh::LeanObject,
    mut v_a_4806_: *mut leanh::LeanObject,
    mut v_a_4807_: *mut leanh::LeanObject,
    mut v_a_4808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v___x_4819_: u8 = 0;
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4830_: u8 = 0;
    let mut v_a_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4834_: u8 = 0;
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_a_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4810_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                leanh::lean_inc(v_mvarId_4804_);
                v___x_4811_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4804_,
                    v___x_4810_,
                    v_a_4805_,
                    v_a_4806_,
                    v_a_4807_,
                    v_a_4808_,
                );
                if leanh::lean_obj_tag(v___x_4811_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4811_, 1);
                    leanh::lean_inc(v_mvarId_4804_);
                    v___x_4812_ = l_Lean_MVarId_getType(
                        v_mvarId_4804_,
                        v_a_4805_,
                        v_a_4806_,
                        v_a_4807_,
                        v_a_4808_,
                    );
                    if leanh::lean_obj_tag(v___x_4812_) == 0 {
                        v_a_4813_ = leanh::lean_ctor_get(v___x_4812_, 0);
                        leanh::lean_inc(v_a_4813_);
                        leanh::lean_dec_ref_known(v___x_4812_, 1);
                        v___x_4814_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_4813_, v_a_4806_);
                        v_a_4815_ = leanh::lean_ctor_get(v___x_4814_, 0);
                        v_isSharedCheck_4830_ =
                            (!leanh::lean_is_exclusive(v___x_4814_)) as u8;
                        if v_isSharedCheck_4830_ == 0 {
                            v___x_4817_ = v___x_4814_;
                            v_isShared_4818_ = v_isSharedCheck_4830_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4815_);
                            leanh::lean_dec(v___x_4814_);
                            v___x_4817_ = leanh::lean_box(0);
                            v_isShared_4818_ = v_isSharedCheck_4830_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_4804_);
                        v_a_4831_ = leanh::lean_ctor_get(v___x_4812_, 0);
                        v_isSharedCheck_4838_ =
                            (!leanh::lean_is_exclusive(v___x_4812_)) as u8;
                        if v_isSharedCheck_4838_ == 0 {
                            v___x_4833_ = v___x_4812_;
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4831_);
                            leanh::lean_dec(v___x_4812_);
                            v___x_4833_ = leanh::lean_box(0);
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_4804_);
                    v_a_4839_ = leanh::lean_ctor_get(v___x_4811_, 0);
                    v_isSharedCheck_4846_ = (!leanh::lean_is_exclusive(v___x_4811_)) as u8;
                    if v_isSharedCheck_4846_ == 0 {
                        v___x_4841_ = v___x_4811_;
                        v_isShared_4842_ = v_isSharedCheck_4846_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4839_);
                        leanh::lean_dec(v___x_4811_);
                        v___x_4841_ = leanh::lean_box(0);
                        v_isShared_4842_ = v_isSharedCheck_4846_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4819_ = l_Lean_Expr_hasExprMVar(v_a_4815_);
                if v___x_4819_ == 0 {
                    leanh::lean_dec(v_a_4815_);
                    if v_isShared_4818_ == 0 {
                        leanh::lean_ctor_set(v___x_4817_, 0, v_mvarId_4804_);
                        v___x_4821_ = v___x_4817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_mvarId_4804_);
                        v___x_4821_ = v_reuseFailAlloc_4822_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4817_);
                    v___x_4823_ = 0;
                    v___x_4824_ = leanh::lean_box((v___x_4823_) as usize);
                    v___x_4825_ = leanh::lean_box((v___x_4819_) as usize);
                    v___f_4826_ = leanh::lean_alloc_closure(
                        l_Lean_MVarId_abstractMVars___lam__0___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4826_, 0, v___x_4824_);
                    leanh::lean_closure_set(v___f_4826_, 1, v___x_4825_);
                    v___x_4827_ = leanh::lean_box((v___x_4823_) as usize);
                    leanh::lean_inc(v_mvarId_4804_);
                    v___f_4828_ = leanh::lean_alloc_closure(
                        l_Lean_MVarId_abstractMVars___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    leanh::lean_closure_set(v___f_4828_, 0, v_a_4815_);
                    leanh::lean_closure_set(v___f_4828_, 1, v___x_4827_);
                    leanh::lean_closure_set(v___f_4828_, 2, v___f_4826_);
                    leanh::lean_closure_set(v___f_4828_, 3, v_mvarId_4804_);
                    v___x_4829_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_4804_, v___f_4828_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
                    return v___x_4829_;
                }
            }
            2 => {
                return v___x_4821_;
            }
            3 => {
                if v_isShared_4834_ == 0 {
                    v___x_4836_ = v___x_4833_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
                    v___x_4836_ = v_reuseFailAlloc_4837_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4836_;
            }
            5 => {
                if v_isShared_4842_ == 0 {
                    v___x_4844_ = v___x_4841_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
                    v___x_4844_ = v_reuseFailAlloc_4845_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_abstractMVars___boxed(
    mut v_mvarId_4847_: *mut leanh::LeanObject,
    mut v_a_4848_: *mut leanh::LeanObject,
    mut v_a_4849_: *mut leanh::LeanObject,
    mut v_a_4850_: *mut leanh::LeanObject,
    mut v_a_4851_: *mut leanh::LeanObject,
    mut v_a_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4853_ =
        l_Lean_MVarId_abstractMVars(v_mvarId_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
    leanh::lean_dec(v_a_4851_);
    leanh::lean_dec_ref(v_a_4850_);
    leanh::lean_dec(v_a_4849_);
    leanh::lean_dec_ref(v_a_4848_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_MVarId_transformTarget___lam__0(
    mut v_mvarId_4854_: *mut leanh::LeanObject,
    mut v___x_4855_: *mut leanh::LeanObject,
    mut v_f_4856_: *mut leanh::LeanObject,
    mut v___y_4857_: *mut leanh::LeanObject,
    mut v___y_4858_: *mut leanh::LeanObject,
    mut v___y_4859_: *mut leanh::LeanObject,
    mut v___y_4860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_unused_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4888_: u8 = 0;
    let mut v_a_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4892_: u8 = 0;
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut v_a_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_a_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v_a_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_4854_);
                v___x_4862_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4854_,
                    v___x_4855_,
                    v___y_4857_,
                    v___y_4858_,
                    v___y_4859_,
                    v___y_4860_,
                );
                if leanh::lean_obj_tag(v___x_4862_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4862_, 1);
                    leanh::lean_inc(v_mvarId_4854_);
                    v___x_4863_ = l_Lean_MVarId_getTag(
                        v_mvarId_4854_,
                        v___y_4857_,
                        v___y_4858_,
                        v___y_4859_,
                        v___y_4860_,
                    );
                    if leanh::lean_obj_tag(v___x_4863_) == 0 {
                        v_a_4864_ = leanh::lean_ctor_get(v___x_4863_, 0);
                        leanh::lean_inc(v_a_4864_);
                        leanh::lean_dec_ref_known(v___x_4863_, 1);
                        leanh::lean_inc(v_mvarId_4854_);
                        v___x_4865_ = l_Lean_MVarId_getType(
                            v_mvarId_4854_,
                            v___y_4857_,
                            v___y_4858_,
                            v___y_4859_,
                            v___y_4860_,
                        );
                        if leanh::lean_obj_tag(v___x_4865_) == 0 {
                            v_a_4866_ = leanh::lean_ctor_get(v___x_4865_, 0);
                            leanh::lean_inc(v_a_4866_);
                            leanh::lean_dec_ref_known(v___x_4865_, 1);
                            leanh::lean_inc(v___y_4860_);
                            leanh::lean_inc_ref(v___y_4859_);
                            leanh::lean_inc(v___y_4858_);
                            leanh::lean_inc_ref(v___y_4857_);
                            v___x_4867_ = leanh::lean_apply_6(
                                v_f_4856_,
                                v_a_4866_,
                                v___y_4857_,
                                v___y_4858_,
                                v___y_4859_,
                                v___y_4860_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_4867_) == 0 {
                                v_a_4868_ = leanh::lean_ctor_get(v___x_4867_, 0);
                                leanh::lean_inc(v_a_4868_);
                                leanh::lean_dec_ref_known(v___x_4867_, 1);
                                v___x_4869_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v_a_4868_,
                                    v_a_4864_,
                                    v___y_4857_,
                                    v___y_4858_,
                                    v___y_4859_,
                                    v___y_4860_,
                                );
                                leanh::lean_dec(v___y_4860_);
                                leanh::lean_dec_ref(v___y_4859_);
                                leanh::lean_dec_ref(v___y_4857_);
                                if leanh::lean_obj_tag(v___x_4869_) == 0 {
                                    v_a_4870_ = leanh::lean_ctor_get(v___x_4869_, 0);
                                    leanh::lean_inc_n(v_a_4870_, 2);
                                    leanh::lean_dec_ref_known(v___x_4869_, 1);
                                    v___x_4871_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_4854_, v_a_4870_, v___y_4858_);
                                    leanh::lean_dec(v___y_4858_);
                                    v_isSharedCheck_4879_ =
                                        (!leanh::lean_is_exclusive(v___x_4871_)) as u8;
                                    if v_isSharedCheck_4879_ == 0 {
                                        v_unused_4880_ =
                                            leanh::lean_ctor_get(v___x_4871_, 0);
                                        leanh::lean_dec(v_unused_4880_);
                                        v___x_4873_ = v___x_4871_;
                                        v_isShared_4874_ = v_isSharedCheck_4879_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_4871_);
                                        v___x_4873_ = leanh::lean_box(0);
                                        v_isShared_4874_ = v_isSharedCheck_4879_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___y_4858_);
                                    leanh::lean_dec(v_mvarId_4854_);
                                    v_a_4881_ = leanh::lean_ctor_get(v___x_4869_, 0);
                                    v_isSharedCheck_4888_ =
                                        (!leanh::lean_is_exclusive(v___x_4869_)) as u8;
                                    if v_isSharedCheck_4888_ == 0 {
                                        v___x_4883_ = v___x_4869_;
                                        v_isShared_4884_ = v_isSharedCheck_4888_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4881_);
                                        leanh::lean_dec(v___x_4869_);
                                        v___x_4883_ = leanh::lean_box(0);
                                        v_isShared_4884_ = v_isSharedCheck_4888_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_4864_);
                                leanh::lean_dec(v___y_4860_);
                                leanh::lean_dec_ref(v___y_4859_);
                                leanh::lean_dec(v___y_4858_);
                                leanh::lean_dec_ref(v___y_4857_);
                                leanh::lean_dec(v_mvarId_4854_);
                                v_a_4889_ = leanh::lean_ctor_get(v___x_4867_, 0);
                                v_isSharedCheck_4896_ =
                                    (!leanh::lean_is_exclusive(v___x_4867_)) as u8;
                                if v_isSharedCheck_4896_ == 0 {
                                    v___x_4891_ = v___x_4867_;
                                    v_isShared_4892_ = v_isSharedCheck_4896_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4889_);
                                    leanh::lean_dec(v___x_4867_);
                                    v___x_4891_ = leanh::lean_box(0);
                                    v_isShared_4892_ = v_isSharedCheck_4896_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4864_);
                            leanh::lean_dec(v___y_4860_);
                            leanh::lean_dec_ref(v___y_4859_);
                            leanh::lean_dec(v___y_4858_);
                            leanh::lean_dec_ref(v___y_4857_);
                            leanh::lean_dec_ref(v_f_4856_);
                            leanh::lean_dec(v_mvarId_4854_);
                            v_a_4897_ = leanh::lean_ctor_get(v___x_4865_, 0);
                            v_isSharedCheck_4904_ =
                                (!leanh::lean_is_exclusive(v___x_4865_)) as u8;
                            if v_isSharedCheck_4904_ == 0 {
                                v___x_4899_ = v___x_4865_;
                                v_isShared_4900_ = v_isSharedCheck_4904_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4897_);
                                leanh::lean_dec(v___x_4865_);
                                v___x_4899_ = leanh::lean_box(0);
                                v_isShared_4900_ = v_isSharedCheck_4904_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_4860_);
                        leanh::lean_dec_ref(v___y_4859_);
                        leanh::lean_dec(v___y_4858_);
                        leanh::lean_dec_ref(v___y_4857_);
                        leanh::lean_dec_ref(v_f_4856_);
                        leanh::lean_dec(v_mvarId_4854_);
                        v_a_4905_ = leanh::lean_ctor_get(v___x_4863_, 0);
                        v_isSharedCheck_4912_ =
                            (!leanh::lean_is_exclusive(v___x_4863_)) as u8;
                        if v_isSharedCheck_4912_ == 0 {
                            v___x_4907_ = v___x_4863_;
                            v_isShared_4908_ = v_isSharedCheck_4912_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4905_);
                            leanh::lean_dec(v___x_4863_);
                            v___x_4907_ = leanh::lean_box(0);
                            v_isShared_4908_ = v_isSharedCheck_4912_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_4860_);
                    leanh::lean_dec_ref(v___y_4859_);
                    leanh::lean_dec(v___y_4858_);
                    leanh::lean_dec_ref(v___y_4857_);
                    leanh::lean_dec_ref(v_f_4856_);
                    leanh::lean_dec(v_mvarId_4854_);
                    v_a_4913_ = leanh::lean_ctor_get(v___x_4862_, 0);
                    v_isSharedCheck_4920_ = (!leanh::lean_is_exclusive(v___x_4862_)) as u8;
                    if v_isSharedCheck_4920_ == 0 {
                        v___x_4915_ = v___x_4862_;
                        v_isShared_4916_ = v_isSharedCheck_4920_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4913_);
                        leanh::lean_dec(v___x_4862_);
                        v___x_4915_ = leanh::lean_box(0);
                        v_isShared_4916_ = v_isSharedCheck_4920_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4875_ = l_Lean_Expr_mvarId_x21(v_a_4870_);
                leanh::lean_dec(v_a_4870_);
                if v_isShared_4874_ == 0 {
                    leanh::lean_ctor_set(v___x_4873_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4877_;
            }
            3 => {
                if v_isShared_4884_ == 0 {
                    v___x_4886_ = v___x_4883_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4887_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
                    v___x_4886_ = v_reuseFailAlloc_4887_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4886_;
            }
            5 => {
                if v_isShared_4892_ == 0 {
                    v___x_4894_ = v___x_4891_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4895_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
                    v___x_4894_ = v_reuseFailAlloc_4895_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4894_;
            }
            7 => {
                if v_isShared_4900_ == 0 {
                    v___x_4902_ = v___x_4899_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4903_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
                    v___x_4902_ = v_reuseFailAlloc_4903_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4902_;
            }
            9 => {
                if v_isShared_4908_ == 0 {
                    v___x_4910_ = v___x_4907_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
                    v___x_4910_ = v_reuseFailAlloc_4911_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4910_;
            }
            11 => {
                if v_isShared_4916_ == 0 {
                    v___x_4918_ = v___x_4915_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4919_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
                    v___x_4918_ = v_reuseFailAlloc_4919_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_transformTarget___lam__0___boxed(
    mut v_mvarId_4921_: *mut leanh::LeanObject,
    mut v___x_4922_: *mut leanh::LeanObject,
    mut v_f_4923_: *mut leanh::LeanObject,
    mut v___y_4924_: *mut leanh::LeanObject,
    mut v___y_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4929_ = l_Lean_MVarId_transformTarget___lam__0(
        v_mvarId_4921_,
        v___x_4922_,
        v_f_4923_,
        v___y_4924_,
        v___y_4925_,
        v___y_4926_,
        v___y_4927_,
    );
    return v_res_4929_;
}
pub unsafe fn l_Lean_MVarId_transformTarget(
    mut v_mvarId_4930_: *mut leanh::LeanObject,
    mut v_f_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
    mut v_a_4935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4937_ = l_Lean_MVarId_ensureNoMVar___closed__1;
    leanh::lean_inc(v_mvarId_4930_);
    v___f_4938_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_transformTarget___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_4938_, 0, v_mvarId_4930_);
    leanh::lean_closure_set(v___f_4938_, 1, v___x_4937_);
    leanh::lean_closure_set(v___f_4938_, 2, v_f_4931_);
    v___x_4939_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
        v_mvarId_4930_,
        v___f_4938_,
        v_a_4932_,
        v_a_4933_,
        v_a_4934_,
        v_a_4935_,
    );
    return v___x_4939_;
}
pub unsafe fn l_Lean_MVarId_transformTarget___boxed(
    mut v_mvarId_4940_: *mut leanh::LeanObject,
    mut v_f_4941_: *mut leanh::LeanObject,
    mut v_a_4942_: *mut leanh::LeanObject,
    mut v_a_4943_: *mut leanh::LeanObject,
    mut v_a_4944_: *mut leanh::LeanObject,
    mut v_a_4945_: *mut leanh::LeanObject,
    mut v_a_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_MVarId_transformTarget(
        v_mvarId_4940_,
        v_f_4941_,
        v_a_4942_,
        v_a_4943_,
        v_a_4944_,
        v_a_4945_,
    );
    leanh::lean_dec(v_a_4945_);
    leanh::lean_dec_ref(v_a_4944_);
    leanh::lean_dec(v_a_4943_);
    leanh::lean_dec_ref(v_a_4942_);
    return v_res_4947_;
}
pub unsafe fn l_Lean_MVarId_unfoldReducible(
    mut v_mvarId_4949_: *mut leanh::LeanObject,
    mut v_a_4950_: *mut leanh::LeanObject,
    mut v_a_4951_: *mut leanh::LeanObject,
    mut v_a_4952_: *mut leanh::LeanObject,
    mut v_a_4953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ = l_Lean_MVarId_unfoldReducible___closed__0;
    v___x_4956_ = l_Lean_MVarId_transformTarget(
        v_mvarId_4949_,
        v___x_4955_,
        v_a_4950_,
        v_a_4951_,
        v_a_4952_,
        v_a_4953_,
    );
    return v___x_4956_;
}
pub unsafe fn l_Lean_MVarId_unfoldReducible___boxed(
    mut v_mvarId_4957_: *mut leanh::LeanObject,
    mut v_a_4958_: *mut leanh::LeanObject,
    mut v_a_4959_: *mut leanh::LeanObject,
    mut v_a_4960_: *mut leanh::LeanObject,
    mut v_a_4961_: *mut leanh::LeanObject,
    mut v_a_4962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4963_ =
        l_Lean_MVarId_unfoldReducible(v_mvarId_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_);
    leanh::lean_dec(v_a_4961_);
    leanh::lean_dec_ref(v_a_4960_);
    leanh::lean_dec(v_a_4959_);
    leanh::lean_dec_ref(v_a_4958_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_MVarId_betaReduce___lam__0(
    mut v_x_4964_: *mut leanh::LeanObject,
    mut v___y_4965_: *mut leanh::LeanObject,
    mut v___y_4966_: *mut leanh::LeanObject,
    mut v___y_4967_: *mut leanh::LeanObject,
    mut v___y_4968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4970_ = l_Lean_Core_betaReduce(v_x_4964_, v___y_4967_, v___y_4968_);
    return v___x_4970_;
}
pub unsafe fn l_Lean_MVarId_betaReduce___lam__0___boxed(
    mut v_x_4971_: *mut leanh::LeanObject,
    mut v___y_4972_: *mut leanh::LeanObject,
    mut v___y_4973_: *mut leanh::LeanObject,
    mut v___y_4974_: *mut leanh::LeanObject,
    mut v___y_4975_: *mut leanh::LeanObject,
    mut v___y_4976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Lean_MVarId_betaReduce___lam__0(
        v_x_4971_,
        v___y_4972_,
        v___y_4973_,
        v___y_4974_,
        v___y_4975_,
    );
    leanh::lean_dec(v___y_4975_);
    leanh::lean_dec_ref(v___y_4974_);
    leanh::lean_dec(v___y_4973_);
    leanh::lean_dec_ref(v___y_4972_);
    return v_res_4977_;
}
pub unsafe fn l_Lean_MVarId_betaReduce(
    mut v_mvarId_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
    mut v_a_4981_: *mut leanh::LeanObject,
    mut v_a_4982_: *mut leanh::LeanObject,
    mut v_a_4983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4985_ = l_Lean_MVarId_betaReduce___closed__0;
    v___x_4986_ = l_Lean_MVarId_transformTarget(
        v_mvarId_4979_,
        v___f_4985_,
        v_a_4980_,
        v_a_4981_,
        v_a_4982_,
        v_a_4983_,
    );
    return v___x_4986_;
}
pub unsafe fn l_Lean_MVarId_betaReduce___boxed(
    mut v_mvarId_4987_: *mut leanh::LeanObject,
    mut v_a_4988_: *mut leanh::LeanObject,
    mut v_a_4989_: *mut leanh::LeanObject,
    mut v_a_4990_: *mut leanh::LeanObject,
    mut v_a_4991_: *mut leanh::LeanObject,
    mut v_a_4992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4993_ =
        l_Lean_MVarId_betaReduce(v_mvarId_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
    leanh::lean_dec(v_a_4991_);
    leanh::lean_dec_ref(v_a_4990_);
    leanh::lean_dec(v_a_4989_);
    leanh::lean_dec_ref(v_a_4988_);
    return v_res_4993_;
}
pub unsafe fn _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4997_ = leanh::lean_box(0);
    v___x_4998_ = l_Lean_MVarId_byContra_x3f___lam__0___closed__1;
    v___x_4999_ = l_Lean_mkConst(v___x_4998_, v___x_4997_);
    return v___x_4999_;
}
pub unsafe fn _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5005_ = leanh::lean_box(0);
    v___x_5006_ = l_Lean_MVarId_byContra_x3f___lam__0___closed__5;
    v___x_5007_ = l_Lean_mkConst(v___x_5006_, v___x_5005_);
    return v___x_5007_;
}
pub unsafe fn l_Lean_MVarId_byContra_x3f___lam__0(
    mut v_mvarId_5008_: *mut leanh::LeanObject,
    mut v___x_5009_: *mut leanh::LeanObject,
    mut v___y_5010_: *mut leanh::LeanObject,
    mut v___y_5011_: *mut leanh::LeanObject,
    mut v___y_5012_: *mut leanh::LeanObject,
    mut v___y_5013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: u8 = 0;
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5041_: u8 = 0;
    let mut v_unused_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5046_: u8 = 0;
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_a_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_a_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5062_: u8 = 0;
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5066_: u8 = 0;
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_a_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut v_a_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_5008_);
                v___x_5015_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5008_,
                    v___x_5009_,
                    v___y_5010_,
                    v___y_5011_,
                    v___y_5012_,
                    v___y_5013_,
                );
                if leanh::lean_obj_tag(v___x_5015_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5015_, 1);
                    leanh::lean_inc(v_mvarId_5008_);
                    v___x_5016_ = l_Lean_MVarId_getType(
                        v_mvarId_5008_,
                        v___y_5010_,
                        v___y_5011_,
                        v___y_5012_,
                        v___y_5013_,
                    );
                    if leanh::lean_obj_tag(v___x_5016_) == 0 {
                        v_a_5017_ = leanh::lean_ctor_get(v___x_5016_, 0);
                        v_isSharedCheck_5071_ =
                            (!leanh::lean_is_exclusive(v___x_5016_)) as u8;
                        if v_isSharedCheck_5071_ == 0 {
                            v___x_5019_ = v___x_5016_;
                            v_isShared_5020_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5017_);
                            leanh::lean_dec(v___x_5016_);
                            v___x_5019_ = leanh::lean_box(0);
                            v_isShared_5020_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_5008_);
                        v_a_5072_ = leanh::lean_ctor_get(v___x_5016_, 0);
                        v_isSharedCheck_5079_ =
                            (!leanh::lean_is_exclusive(v___x_5016_)) as u8;
                        if v_isSharedCheck_5079_ == 0 {
                            v___x_5074_ = v___x_5016_;
                            v_isShared_5075_ = v_isSharedCheck_5079_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5072_);
                            leanh::lean_dec(v___x_5016_);
                            v___x_5074_ = leanh::lean_box(0);
                            v_isShared_5075_ = v_isSharedCheck_5079_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_5008_);
                    v_a_5080_ = leanh::lean_ctor_get(v___x_5015_, 0);
                    v_isSharedCheck_5087_ = (!leanh::lean_is_exclusive(v___x_5015_)) as u8;
                    if v_isSharedCheck_5087_ == 0 {
                        v___x_5082_ = v___x_5015_;
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5080_);
                        leanh::lean_dec(v___x_5015_);
                        v___x_5082_ = leanh::lean_box(0);
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_5017_);
                v___x_5021_ = l_Lean_Expr_isFalse(v_a_5017_);
                if v___x_5021_ == 0 {
                    leanh::lean_del_object(v___x_5019_);
                    leanh::lean_inc(v_a_5017_);
                    v___x_5022_ = l_Lean_mkNot(v_a_5017_);
                    v___x_5023_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_byContra_x3f___lam__0___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once
                        ),
                        _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2,
                    );
                    v___x_5024_ =
                        l_Lean_mkArrow(v___x_5022_, v___x_5023_, v___y_5012_, v___y_5013_);
                    if leanh::lean_obj_tag(v___x_5024_) == 0 {
                        v_a_5025_ = leanh::lean_ctor_get(v___x_5024_, 0);
                        leanh::lean_inc(v_a_5025_);
                        leanh::lean_dec_ref_known(v___x_5024_, 1);
                        leanh::lean_inc(v_mvarId_5008_);
                        v___x_5026_ = l_Lean_MVarId_getTag(
                            v_mvarId_5008_,
                            v___y_5010_,
                            v___y_5011_,
                            v___y_5012_,
                            v___y_5013_,
                        );
                        if leanh::lean_obj_tag(v___x_5026_) == 0 {
                            v_a_5027_ = leanh::lean_ctor_get(v___x_5026_, 0);
                            leanh::lean_inc(v_a_5027_);
                            leanh::lean_dec_ref_known(v___x_5026_, 1);
                            v___x_5028_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_5025_,
                                v_a_5027_,
                                v___y_5010_,
                                v___y_5011_,
                                v___y_5012_,
                                v___y_5013_,
                            );
                            if leanh::lean_obj_tag(v___x_5028_) == 0 {
                                v_a_5029_ = leanh::lean_ctor_get(v___x_5028_, 0);
                                leanh::lean_inc_n(v_a_5029_, 2);
                                leanh::lean_dec_ref_known(v___x_5028_, 1);
                                v___x_5030_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_byContra_x3f___lam__0___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once
                                    ),
                                    _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6,
                                );
                                v___x_5031_ = l_Lean_mkAppB(v___x_5030_, v_a_5017_, v_a_5029_);
                                v___x_5032_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_5008_, v___x_5031_, v___y_5011_);
                                v_isSharedCheck_5041_ =
                                    (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                                if v_isSharedCheck_5041_ == 0 {
                                    v_unused_5042_ = leanh::lean_ctor_get(v___x_5032_, 0);
                                    leanh::lean_dec(v_unused_5042_);
                                    v___x_5034_ = v___x_5032_;
                                    v_isShared_5035_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_5032_);
                                    v___x_5034_ = leanh::lean_box(0);
                                    v_isShared_5035_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5017_);
                                leanh::lean_dec(v_mvarId_5008_);
                                v_a_5043_ = leanh::lean_ctor_get(v___x_5028_, 0);
                                v_isSharedCheck_5050_ =
                                    (!leanh::lean_is_exclusive(v___x_5028_)) as u8;
                                if v_isSharedCheck_5050_ == 0 {
                                    v___x_5045_ = v___x_5028_;
                                    v_isShared_5046_ = v_isSharedCheck_5050_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5043_);
                                    leanh::lean_dec(v___x_5028_);
                                    v___x_5045_ = leanh::lean_box(0);
                                    v_isShared_5046_ = v_isSharedCheck_5050_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_5025_);
                            leanh::lean_dec(v_a_5017_);
                            leanh::lean_dec(v_mvarId_5008_);
                            v_a_5051_ = leanh::lean_ctor_get(v___x_5026_, 0);
                            v_isSharedCheck_5058_ =
                                (!leanh::lean_is_exclusive(v___x_5026_)) as u8;
                            if v_isSharedCheck_5058_ == 0 {
                                v___x_5053_ = v___x_5026_;
                                v_isShared_5054_ = v_isSharedCheck_5058_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5051_);
                                leanh::lean_dec(v___x_5026_);
                                v___x_5053_ = leanh::lean_box(0);
                                v_isShared_5054_ = v_isSharedCheck_5058_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5017_);
                        leanh::lean_dec(v_mvarId_5008_);
                        v_a_5059_ = leanh::lean_ctor_get(v___x_5024_, 0);
                        v_isSharedCheck_5066_ =
                            (!leanh::lean_is_exclusive(v___x_5024_)) as u8;
                        if v_isSharedCheck_5066_ == 0 {
                            v___x_5061_ = v___x_5024_;
                            v_isShared_5062_ = v_isSharedCheck_5066_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5059_);
                            leanh::lean_dec(v___x_5024_);
                            v___x_5061_ = leanh::lean_box(0);
                            v_isShared_5062_ = v_isSharedCheck_5066_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5017_);
                    leanh::lean_dec(v_mvarId_5008_);
                    v___x_5067_ = leanh::lean_box(0);
                    if v_isShared_5020_ == 0 {
                        leanh::lean_ctor_set(v___x_5019_, 0, v___x_5067_);
                        v___x_5069_ = v___x_5019_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5070_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
                        v___x_5069_ = v_reuseFailAlloc_5070_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5036_ = l_Lean_Expr_mvarId_x21(v_a_5029_);
                leanh::lean_dec(v_a_5029_);
                v___x_5037_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5037_, 0, v___x_5036_);
                if v_isShared_5035_ == 0 {
                    leanh::lean_ctor_set(v___x_5034_, 0, v___x_5037_);
                    v___x_5039_ = v___x_5034_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5040_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
                    v___x_5039_ = v_reuseFailAlloc_5040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5039_;
            }
            4 => {
                if v_isShared_5046_ == 0 {
                    v___x_5048_ = v___x_5045_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
                    v___x_5048_ = v_reuseFailAlloc_5049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5048_;
            }
            6 => {
                if v_isShared_5054_ == 0 {
                    v___x_5056_ = v___x_5053_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
                    v___x_5056_ = v_reuseFailAlloc_5057_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5056_;
            }
            8 => {
                if v_isShared_5062_ == 0 {
                    v___x_5064_ = v___x_5061_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
                    v___x_5064_ = v_reuseFailAlloc_5065_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5064_;
            }
            10 => {
                return v___x_5069_;
            }
            11 => {
                if v_isShared_5075_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
                    v___x_5077_ = v_reuseFailAlloc_5078_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5077_;
            }
            13 => {
                if v_isShared_5083_ == 0 {
                    v___x_5085_ = v___x_5082_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_byContra_x3f___lam__0___boxed(
    mut v_mvarId_5088_: *mut leanh::LeanObject,
    mut v___x_5089_: *mut leanh::LeanObject,
    mut v___y_5090_: *mut leanh::LeanObject,
    mut v___y_5091_: *mut leanh::LeanObject,
    mut v___y_5092_: *mut leanh::LeanObject,
    mut v___y_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5095_ = l_Lean_MVarId_byContra_x3f___lam__0(
        v_mvarId_5088_,
        v___x_5089_,
        v___y_5090_,
        v___y_5091_,
        v___y_5092_,
        v___y_5093_,
    );
    leanh::lean_dec(v___y_5093_);
    leanh::lean_dec_ref(v___y_5092_);
    leanh::lean_dec(v___y_5091_);
    leanh::lean_dec_ref(v___y_5090_);
    return v_res_5095_;
}
pub unsafe fn l_Lean_MVarId_byContra_x3f(
    mut v_mvarId_5100_: *mut leanh::LeanObject,
    mut v_a_5101_: *mut leanh::LeanObject,
    mut v_a_5102_: *mut leanh::LeanObject,
    mut v_a_5103_: *mut leanh::LeanObject,
    mut v_a_5104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Lean_MVarId_byContra_x3f___closed__1;
    leanh::lean_inc(v_mvarId_5100_);
    v___f_5107_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_byContra_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_5107_, 0, v_mvarId_5100_);
    leanh::lean_closure_set(v___f_5107_, 1, v___x_5106_);
    v___x_5108_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
        v_mvarId_5100_,
        v___f_5107_,
        v_a_5101_,
        v_a_5102_,
        v_a_5103_,
        v_a_5104_,
    );
    return v___x_5108_;
}
pub unsafe fn l_Lean_MVarId_byContra_x3f___boxed(
    mut v_mvarId_5109_: *mut leanh::LeanObject,
    mut v_a_5110_: *mut leanh::LeanObject,
    mut v_a_5111_: *mut leanh::LeanObject,
    mut v_a_5112_: *mut leanh::LeanObject,
    mut v_a_5113_: *mut leanh::LeanObject,
    mut v_a_5114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5115_ =
        l_Lean_MVarId_byContra_x3f(v_mvarId_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_);
    leanh::lean_dec(v_a_5113_);
    leanh::lean_dec_ref(v_a_5112_);
    leanh::lean_dec(v_a_5111_);
    leanh::lean_dec_ref(v_a_5110_);
    return v_res_5115_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5117_ =
        l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0;
    v___x_5118_ = l_Lean_stringToMessageData(v___x_5117_);
    return v___x_5118_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5120_ =
        l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2;
    v___x_5121_ = l_Lean_stringToMessageData(v___x_5120_);
    return v___x_5121_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5123_ =
        l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4;
    v___x_5124_ = l_Lean_stringToMessageData(v___x_5123_);
    return v___x_5124_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(
    mut v_as_x27_5125_: *mut leanh::LeanObject,
    mut v_b_5126_: *mut leanh::LeanObject,
    mut v___y_5127_: *mut leanh::LeanObject,
    mut v___y_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
    mut v___y_5130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5140_: u8 = 0;
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5169_: u8 = 0;
    let mut v_reuseFailAlloc_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5174_: u8 = 0;
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v_isSharedCheck_5179_: u8 = 0;
    let mut v_unused_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: u8 = 0;
    let mut v___x_5182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_5125_) == 0 {
                    v___x_5132_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5132_, 0, v_b_5126_);
                    return v___x_5132_;
                } else {
                    v_head_5133_ = leanh::lean_ctor_get(v_as_x27_5125_, 0);
                    v_tail_5134_ = leanh::lean_ctor_get(v_as_x27_5125_, 1);
                    leanh::lean_inc(v_head_5133_);
                    leanh::lean_inc(v_b_5126_);
                    v___x_5135_ = l_Lean_MVarId_clear(
                        v_b_5126_,
                        v_head_5133_,
                        v___y_5127_,
                        v___y_5128_,
                        v___y_5129_,
                        v___y_5130_,
                    );
                    if leanh::lean_obj_tag(v___x_5135_) == 0 {
                        leanh::lean_dec(v_b_5126_);
                        v_a_5136_ = leanh::lean_ctor_get(v___x_5135_, 0);
                        leanh::lean_inc(v_a_5136_);
                        leanh::lean_dec_ref_known(v___x_5135_, 1);
                        v_as_x27_5125_ = v_tail_5134_;
                        v_b_5126_ = v_a_5136_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5138_ = leanh::lean_ctor_get(v___x_5135_, 0);
                        leanh::lean_inc(v_a_5138_);
                        v___x_5181_ = l_Lean_Exception_isInterrupt(v_a_5138_);
                        if v___x_5181_ == 0 {
                            v___x_5182_ = l_Lean_Exception_isRuntime(v_a_5138_);
                            v___y_5140_ = v___x_5182_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_5138_);
                            v___y_5140_ = v___x_5181_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_5140_ == 0 {
                    v_isSharedCheck_5179_ = (!leanh::lean_is_exclusive(v___x_5135_)) as u8;
                    if v_isSharedCheck_5179_ == 0 {
                        v_unused_5180_ = leanh::lean_ctor_get(v___x_5135_, 0);
                        leanh::lean_dec(v_unused_5180_);
                        v___x_5142_ = v___x_5135_;
                        v_isShared_5143_ = v_isSharedCheck_5179_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5135_);
                        v___x_5142_ = leanh::lean_box(0);
                        v_isShared_5143_ = v_isSharedCheck_5179_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_5126_);
                    return v___x_5135_;
                }
            }
            2 => {
                leanh::lean_inc(v_head_5133_);
                v___x_5144_ = l_Lean_FVarId_getDecl___redArg(
                    v_head_5133_,
                    v___y_5127_,
                    v___y_5129_,
                    v___y_5130_,
                );
                if leanh::lean_obj_tag(v___x_5144_) == 0 {
                    v_a_5145_ = leanh::lean_ctor_get(v___x_5144_, 0);
                    leanh::lean_inc(v_a_5145_);
                    leanh::lean_dec_ref_known(v___x_5144_, 1);
                    v___x_5146_ = l_Lean_LocalDecl_isAuxDecl(v_a_5145_);
                    if v___x_5146_ == 0 {
                        leanh::lean_dec(v_a_5145_);
                        leanh::lean_del_object(v___x_5142_);
                        v_as_x27_5125_ = v_tail_5134_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5148_ = l_Lean_LocalDecl_userName(v_a_5145_);
                        leanh::lean_dec(v_a_5145_);
                        v___x_5149_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                        v___x_5150_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
                        v___x_5151_ = l_Lean_MessageData_ofName(v___x_5148_);
                        leanh::lean_inc_ref(v___x_5151_);
                        v___x_5152_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5152_, 0, v___x_5150_);
                        leanh::lean_ctor_set(v___x_5152_, 1, v___x_5151_);
                        v___x_5153_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
                        v___x_5154_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5154_, 0, v___x_5152_);
                        leanh::lean_ctor_set(v___x_5154_, 1, v___x_5153_);
                        v___x_5155_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5155_, 0, v___x_5154_);
                        leanh::lean_ctor_set(v___x_5155_, 1, v___x_5151_);
                        v___x_5156_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
                        v___x_5157_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5157_, 0, v___x_5155_);
                        leanh::lean_ctor_set(v___x_5157_, 1, v___x_5156_);
                        if v_isShared_5143_ == 0 {
                            leanh::lean_ctor_set(v___x_5142_, 0, v___x_5157_);
                            v___x_5159_ = v___x_5142_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5170_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5157_);
                            v___x_5159_ = v_reuseFailAlloc_5170_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5142_);
                    leanh::lean_dec(v_b_5126_);
                    v_a_5171_ = leanh::lean_ctor_get(v___x_5144_, 0);
                    v_isSharedCheck_5178_ = (!leanh::lean_is_exclusive(v___x_5144_)) as u8;
                    if v_isSharedCheck_5178_ == 0 {
                        v___x_5173_ = v___x_5144_;
                        v_isShared_5174_ = v_isSharedCheck_5178_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5171_);
                        leanh::lean_dec(v___x_5144_);
                        v___x_5173_ = leanh::lean_box(0);
                        v_isShared_5174_ = v_isSharedCheck_5178_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_b_5126_);
                v___x_5160_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5149_,
                    v_b_5126_,
                    v___x_5159_,
                    v___y_5127_,
                    v___y_5128_,
                    v___y_5129_,
                    v___y_5130_,
                );
                if leanh::lean_obj_tag(v___x_5160_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5160_, 1);
                    v_as_x27_5125_ = v_tail_5134_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_b_5126_);
                    v_a_5162_ = leanh::lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5169_ = (!leanh::lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5169_ == 0 {
                        v___x_5164_ = v___x_5160_;
                        v_isShared_5165_ = v_isSharedCheck_5169_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5162_);
                        leanh::lean_dec(v___x_5160_);
                        v___x_5164_ = leanh::lean_box(0);
                        v_isShared_5165_ = v_isSharedCheck_5169_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5165_ == 0 {
                    v___x_5167_ = v___x_5164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
                    v___x_5167_ = v_reuseFailAlloc_5168_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5167_;
            }
            6 => {
                if v_isShared_5174_ == 0 {
                    v___x_5176_ = v___x_5173_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
                    v___x_5176_ = v_reuseFailAlloc_5177_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(
    mut v_as_x27_5183_: *mut leanh::LeanObject,
    mut v_b_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
    mut v___y_5188_: *mut leanh::LeanObject,
    mut v___y_5189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(
        v_as_x27_5183_,
        v_b_5184_,
        v___y_5185_,
        v___y_5186_,
        v___y_5187_,
        v___y_5188_,
    );
    leanh::lean_dec(v___y_5188_);
    leanh::lean_dec_ref(v___y_5187_);
    leanh::lean_dec(v___y_5186_);
    leanh::lean_dec_ref(v___y_5185_);
    leanh::lean_dec(v_as_x27_5183_);
    return v_res_5190_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_as_5191_: *mut leanh::LeanObject,
    mut v_sz_5192_: usize,
    mut v_i_5193_: usize,
    mut v_b_5194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v_reuseFailAlloc_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut v_unused_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5196_ = lean_usize_dec_lt(v_i_5193_, v_sz_5192_);
                if v___x_5196_ == 0 {
                    v___x_5197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5197_, 0, v_b_5194_);
                    return v___x_5197_;
                } else {
                    v_snd_5198_ = leanh::lean_ctor_get(v_b_5194_, 1);
                    v_isSharedCheck_5216_ = (!leanh::lean_is_exclusive(v_b_5194_)) as u8;
                    if v_isSharedCheck_5216_ == 0 {
                        v_unused_5217_ = leanh::lean_ctor_get(v_b_5194_, 0);
                        leanh::lean_dec(v_unused_5217_);
                        v___x_5200_ = v_b_5194_;
                        v_isShared_5201_ = v_isSharedCheck_5216_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5198_);
                        leanh::lean_dec(v_b_5194_);
                        v___x_5200_ = leanh::lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5216_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5202_ = leanh::lean_box(0);
                v_a_5211_ = lean_array_uget_borrowed(v_as_5191_, v_i_5193_);
                if leanh::lean_obj_tag(v_a_5211_) == 0 {
                    v_a_5204_ = v_snd_5198_;
                    state = 2;
                    continue;
                } else {
                    v_val_5212_ = leanh::lean_ctor_get(v_a_5211_, 0);
                    v___x_5213_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5212_);
                    if v___x_5213_ == 0 {
                        v_a_5204_ = v_snd_5198_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5214_ = l_Lean_LocalDecl_fvarId(v_val_5212_);
                        v___x_5215_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5215_, 0, v___x_5214_);
                        leanh::lean_ctor_set(v___x_5215_, 1, v_snd_5198_);
                        v_a_5204_ = v___x_5215_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5201_ == 0 {
                    leanh::lean_ctor_set(v___x_5200_, 1, v_a_5204_);
                    leanh::lean_ctor_set(v___x_5200_, 0, v___x_5202_);
                    v___x_5206_ = v___x_5200_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5210_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 1, v_a_5204_);
                    v___x_5206_ = v_reuseFailAlloc_5210_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5207_ = 1usize;
                v___x_5208_ = lean_usize_add(v_i_5193_, v___x_5207_);
                v_i_5193_ = v___x_5208_;
                v_b_5194_ = v___x_5206_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_as_5218_: *mut leanh::LeanObject,
    mut v_sz_5219_: *mut leanh::LeanObject,
    mut v_i_5220_: *mut leanh::LeanObject,
    mut v_b_5221_: *mut leanh::LeanObject,
    mut v___y_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5223_: usize = 0;
    let mut v_i_boxed_5224_: usize = 0;
    let mut v_res_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5223_ = leanh::lean_unbox_usize(v_sz_5219_);
    leanh::lean_dec(v_sz_5219_);
    v_i_boxed_5224_ = leanh::lean_unbox_usize(v_i_5220_);
    leanh::lean_dec(v_i_5220_);
    v_res_5225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_5218_, v_sz_boxed_5223_, v_i_boxed_5224_, v_b_5221_);
    leanh::lean_dec_ref(v_as_5218_);
    return v_res_5225_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(
    mut v_as_5226_: *mut leanh::LeanObject,
    mut v_sz_5227_: usize,
    mut v_i_5228_: usize,
    mut v_b_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
    mut v___y_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5235_: u8 = 0;
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: usize = 0;
    let mut v___x_5247_: usize = 0;
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_unused_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_usize_dec_lt(v_i_5228_, v_sz_5227_);
                if v___x_5235_ == 0 {
                    v___x_5236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5236_, 0, v_b_5229_);
                    return v___x_5236_;
                } else {
                    v_snd_5237_ = leanh::lean_ctor_get(v_b_5229_, 1);
                    v_isSharedCheck_5255_ = (!leanh::lean_is_exclusive(v_b_5229_)) as u8;
                    if v_isSharedCheck_5255_ == 0 {
                        v_unused_5256_ = leanh::lean_ctor_get(v_b_5229_, 0);
                        leanh::lean_dec(v_unused_5256_);
                        v___x_5239_ = v_b_5229_;
                        v_isShared_5240_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5237_);
                        leanh::lean_dec(v_b_5229_);
                        v___x_5239_ = leanh::lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5241_ = leanh::lean_box(0);
                v_a_5250_ = lean_array_uget_borrowed(v_as_5226_, v_i_5228_);
                if leanh::lean_obj_tag(v_a_5250_) == 0 {
                    v_a_5243_ = v_snd_5237_;
                    state = 2;
                    continue;
                } else {
                    v_val_5251_ = leanh::lean_ctor_get(v_a_5250_, 0);
                    v___x_5252_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5251_);
                    if v___x_5252_ == 0 {
                        v_a_5243_ = v_snd_5237_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5253_ = l_Lean_LocalDecl_fvarId(v_val_5251_);
                        v___x_5254_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5254_, 0, v___x_5253_);
                        leanh::lean_ctor_set(v___x_5254_, 1, v_snd_5237_);
                        v_a_5243_ = v___x_5254_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5240_ == 0 {
                    leanh::lean_ctor_set(v___x_5239_, 1, v_a_5243_);
                    leanh::lean_ctor_set(v___x_5239_, 0, v___x_5241_);
                    v___x_5245_ = v___x_5239_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5249_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5249_, 0, v___x_5241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5249_, 1, v_a_5243_);
                    v___x_5245_ = v_reuseFailAlloc_5249_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5246_ = 1usize;
                v___x_5247_ = lean_usize_add(v_i_5228_, v___x_5246_);
                v___x_5248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_5226_, v_sz_5227_, v___x_5247_, v___x_5245_);
                return v___x_5248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(
    mut v_as_5257_: *mut leanh::LeanObject,
    mut v_sz_5258_: *mut leanh::LeanObject,
    mut v_i_5259_: *mut leanh::LeanObject,
    mut v_b_5260_: *mut leanh::LeanObject,
    mut v___y_5261_: *mut leanh::LeanObject,
    mut v___y_5262_: *mut leanh::LeanObject,
    mut v___y_5263_: *mut leanh::LeanObject,
    mut v___y_5264_: *mut leanh::LeanObject,
    mut v___y_5265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5266_: usize = 0;
    let mut v_i_boxed_5267_: usize = 0;
    let mut v_res_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5266_ = leanh::lean_unbox_usize(v_sz_5258_);
    leanh::lean_dec(v_sz_5258_);
    v_i_boxed_5267_ = leanh::lean_unbox_usize(v_i_5259_);
    leanh::lean_dec(v_i_5259_);
    v_res_5268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_5257_, v_sz_boxed_5266_, v_i_boxed_5267_, v_b_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
    leanh::lean_dec(v___y_5264_);
    leanh::lean_dec_ref(v___y_5263_);
    leanh::lean_dec(v___y_5262_);
    leanh::lean_dec_ref(v___y_5261_);
    leanh::lean_dec_ref(v_as_5257_);
    return v_res_5268_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(
    mut v_init_5269_: *mut leanh::LeanObject,
    mut v_n_5270_: *mut leanh::LeanObject,
    mut v_b_5271_: *mut leanh::LeanObject,
    mut v___y_5272_: *mut leanh::LeanObject,
    mut v___y_5273_: *mut leanh::LeanObject,
    mut v___y_5274_: *mut leanh::LeanObject,
    mut v___y_5275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5280_: usize = 0;
    let mut v___x_5281_: usize = 0;
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5286_: u8 = 0;
    let mut v_fst_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v_a_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v_vs_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5309_: usize = 0;
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v_fst_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_a_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5330_: u8 = 0;
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_5270_) == 0 {
                    v_cs_5277_ = leanh::lean_ctor_get(v_n_5270_, 0);
                    v___x_5278_ = leanh::lean_box(0);
                    v___x_5279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5279_, 0, v___x_5278_);
                    leanh::lean_ctor_set(v___x_5279_, 1, v_b_5271_);
                    v_sz_5280_ = lean_array_size(v_cs_5277_);
                    v___x_5281_ = 0usize;
                    v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_5269_, v_cs_5277_, v_sz_5280_, v___x_5281_, v___x_5279_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
                    if leanh::lean_obj_tag(v___x_5282_) == 0 {
                        v_a_5283_ = leanh::lean_ctor_get(v___x_5282_, 0);
                        v_isSharedCheck_5297_ =
                            (!leanh::lean_is_exclusive(v___x_5282_)) as u8;
                        if v_isSharedCheck_5297_ == 0 {
                            v___x_5285_ = v___x_5282_;
                            v_isShared_5286_ = v_isSharedCheck_5297_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5283_);
                            leanh::lean_dec(v___x_5282_);
                            v___x_5285_ = leanh::lean_box(0);
                            v_isShared_5286_ = v_isSharedCheck_5297_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5298_ = leanh::lean_ctor_get(v___x_5282_, 0);
                        v_isSharedCheck_5305_ =
                            (!leanh::lean_is_exclusive(v___x_5282_)) as u8;
                        if v_isSharedCheck_5305_ == 0 {
                            v___x_5300_ = v___x_5282_;
                            v_isShared_5301_ = v_isSharedCheck_5305_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5298_);
                            leanh::lean_dec(v___x_5282_);
                            v___x_5300_ = leanh::lean_box(0);
                            v_isShared_5301_ = v_isSharedCheck_5305_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5306_ = leanh::lean_ctor_get(v_n_5270_, 0);
                    v___x_5307_ = leanh::lean_box(0);
                    v___x_5308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5308_, 0, v___x_5307_);
                    leanh::lean_ctor_set(v___x_5308_, 1, v_b_5271_);
                    v_sz_5309_ = lean_array_size(v_vs_5306_);
                    v___x_5310_ = 0usize;
                    v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_5306_, v_sz_5309_, v___x_5310_, v___x_5308_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
                    if leanh::lean_obj_tag(v___x_5311_) == 0 {
                        v_a_5312_ = leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5326_ =
                            (!leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5326_ == 0 {
                            v___x_5314_ = v___x_5311_;
                            v_isShared_5315_ = v_isSharedCheck_5326_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5312_);
                            leanh::lean_dec(v___x_5311_);
                            v___x_5314_ = leanh::lean_box(0);
                            v_isShared_5315_ = v_isSharedCheck_5326_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5327_ = leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5334_ =
                            (!leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5334_ == 0 {
                            v___x_5329_ = v___x_5311_;
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5327_);
                            leanh::lean_dec(v___x_5311_);
                            v___x_5329_ = leanh::lean_box(0);
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5287_ = leanh::lean_ctor_get(v_a_5283_, 0);
                if leanh::lean_obj_tag(v_fst_5287_) == 0 {
                    v_snd_5288_ = leanh::lean_ctor_get(v_a_5283_, 1);
                    leanh::lean_inc(v_snd_5288_);
                    leanh::lean_dec(v_a_5283_);
                    v___x_5289_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5289_, 0, v_snd_5288_);
                    if v_isShared_5286_ == 0 {
                        leanh::lean_ctor_set(v___x_5285_, 0, v___x_5289_);
                        v___x_5291_ = v___x_5285_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5292_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
                        v___x_5291_ = v_reuseFailAlloc_5292_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5287_);
                    leanh::lean_dec(v_a_5283_);
                    v_val_5293_ = leanh::lean_ctor_get(v_fst_5287_, 0);
                    leanh::lean_inc(v_val_5293_);
                    leanh::lean_dec_ref_known(v_fst_5287_, 1);
                    if v_isShared_5286_ == 0 {
                        leanh::lean_ctor_set(v___x_5285_, 0, v_val_5293_);
                        v___x_5295_ = v___x_5285_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_val_5293_);
                        v___x_5295_ = v_reuseFailAlloc_5296_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5291_;
            }
            3 => {
                return v___x_5295_;
            }
            4 => {
                if v_isShared_5301_ == 0 {
                    v___x_5303_ = v___x_5300_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5303_;
            }
            6 => {
                v_fst_5316_ = leanh::lean_ctor_get(v_a_5312_, 0);
                if leanh::lean_obj_tag(v_fst_5316_) == 0 {
                    v_snd_5317_ = leanh::lean_ctor_get(v_a_5312_, 1);
                    leanh::lean_inc(v_snd_5317_);
                    leanh::lean_dec(v_a_5312_);
                    v___x_5318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5318_, 0, v_snd_5317_);
                    if v_isShared_5315_ == 0 {
                        leanh::lean_ctor_set(v___x_5314_, 0, v___x_5318_);
                        v___x_5320_ = v___x_5314_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5321_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5318_);
                        v___x_5320_ = v_reuseFailAlloc_5321_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5316_);
                    leanh::lean_dec(v_a_5312_);
                    v_val_5322_ = leanh::lean_ctor_get(v_fst_5316_, 0);
                    leanh::lean_inc(v_val_5322_);
                    leanh::lean_dec_ref_known(v_fst_5316_, 1);
                    if v_isShared_5315_ == 0 {
                        leanh::lean_ctor_set(v___x_5314_, 0, v_val_5322_);
                        v___x_5324_ = v___x_5314_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_val_5322_);
                        v___x_5324_ = v_reuseFailAlloc_5325_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5320_;
            }
            8 => {
                return v___x_5324_;
            }
            9 => {
                if v_isShared_5330_ == 0 {
                    v___x_5332_ = v___x_5329_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
                    v___x_5332_ = v_reuseFailAlloc_5333_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(
    mut v_init_5335_: *mut leanh::LeanObject,
    mut v_as_5336_: *mut leanh::LeanObject,
    mut v_sz_5337_: usize,
    mut v_i_5338_: usize,
    mut v_b_5339_: *mut leanh::LeanObject,
    mut v___y_5340_: *mut leanh::LeanObject,
    mut v___y_5341_: *mut leanh::LeanObject,
    mut v___y_5342_: *mut leanh::LeanObject,
    mut v___y_5343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5345_: u8 = 0;
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5350_: u8 = 0;
    let mut v_a_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5356_: u8 = 0;
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: usize = 0;
    let mut v___x_5369_: usize = 0;
    let mut v_reuseFailAlloc_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut v_a_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5376_: u8 = 0;
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5380_: u8 = 0;
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut v_unused_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5345_ = lean_usize_dec_lt(v_i_5338_, v_sz_5337_);
                if v___x_5345_ == 0 {
                    v___x_5346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5346_, 0, v_b_5339_);
                    return v___x_5346_;
                } else {
                    v_snd_5347_ = leanh::lean_ctor_get(v_b_5339_, 1);
                    v_isSharedCheck_5381_ = (!leanh::lean_is_exclusive(v_b_5339_)) as u8;
                    if v_isSharedCheck_5381_ == 0 {
                        v_unused_5382_ = leanh::lean_ctor_get(v_b_5339_, 0);
                        leanh::lean_dec(v_unused_5382_);
                        v___x_5349_ = v_b_5339_;
                        v_isShared_5350_ = v_isSharedCheck_5381_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5347_);
                        leanh::lean_dec(v_b_5339_);
                        v___x_5349_ = leanh::lean_box(0);
                        v_isShared_5350_ = v_isSharedCheck_5381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5351_ = lean_array_uget_borrowed(v_as_5336_, v_i_5338_);
                leanh::lean_inc(v_snd_5347_);
                v___x_5352_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_5335_, v_a_5351_, v_snd_5347_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
                if leanh::lean_obj_tag(v___x_5352_) == 0 {
                    v_a_5353_ = leanh::lean_ctor_get(v___x_5352_, 0);
                    v_isSharedCheck_5372_ = (!leanh::lean_is_exclusive(v___x_5352_)) as u8;
                    if v_isSharedCheck_5372_ == 0 {
                        v___x_5355_ = v___x_5352_;
                        v_isShared_5356_ = v_isSharedCheck_5372_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5353_);
                        leanh::lean_dec(v___x_5352_);
                        v___x_5355_ = leanh::lean_box(0);
                        v_isShared_5356_ = v_isSharedCheck_5372_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5349_);
                    leanh::lean_dec(v_snd_5347_);
                    v_a_5373_ = leanh::lean_ctor_get(v___x_5352_, 0);
                    v_isSharedCheck_5380_ = (!leanh::lean_is_exclusive(v___x_5352_)) as u8;
                    if v_isSharedCheck_5380_ == 0 {
                        v___x_5375_ = v___x_5352_;
                        v_isShared_5376_ = v_isSharedCheck_5380_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5373_);
                        leanh::lean_dec(v___x_5352_);
                        v___x_5375_ = leanh::lean_box(0);
                        v_isShared_5376_ = v_isSharedCheck_5380_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5353_) == 0 {
                    v___x_5357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5357_, 0, v_a_5353_);
                    if v_isShared_5350_ == 0 {
                        leanh::lean_ctor_set(v___x_5349_, 0, v___x_5357_);
                        v___x_5359_ = v___x_5349_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5363_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5357_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_snd_5347_);
                        v___x_5359_ = v_reuseFailAlloc_5363_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5355_);
                    leanh::lean_dec(v_snd_5347_);
                    v_a_5364_ = leanh::lean_ctor_get(v_a_5353_, 0);
                    leanh::lean_inc(v_a_5364_);
                    leanh::lean_dec_ref_known(v_a_5353_, 1);
                    v___x_5365_ = leanh::lean_box(0);
                    if v_isShared_5350_ == 0 {
                        leanh::lean_ctor_set(v___x_5349_, 1, v_a_5364_);
                        leanh::lean_ctor_set(v___x_5349_, 0, v___x_5365_);
                        v___x_5367_ = v___x_5349_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5365_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 1, v_a_5364_);
                        v___x_5367_ = v_reuseFailAlloc_5371_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5356_ == 0 {
                    leanh::lean_ctor_set(v___x_5355_, 0, v___x_5359_);
                    v___x_5361_ = v___x_5355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5362_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5359_);
                    v___x_5361_ = v_reuseFailAlloc_5362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5361_;
            }
            5 => {
                v___x_5368_ = 1usize;
                v___x_5369_ = lean_usize_add(v_i_5338_, v___x_5368_);
                v_i_5338_ = v___x_5369_;
                v_b_5339_ = v___x_5367_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5376_ == 0 {
                    v___x_5378_ = v___x_5375_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5379_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
                    v___x_5378_ = v_reuseFailAlloc_5379_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(
    mut v_init_5383_: *mut leanh::LeanObject,
    mut v_as_5384_: *mut leanh::LeanObject,
    mut v_sz_5385_: *mut leanh::LeanObject,
    mut v_i_5386_: *mut leanh::LeanObject,
    mut v_b_5387_: *mut leanh::LeanObject,
    mut v___y_5388_: *mut leanh::LeanObject,
    mut v___y_5389_: *mut leanh::LeanObject,
    mut v___y_5390_: *mut leanh::LeanObject,
    mut v___y_5391_: *mut leanh::LeanObject,
    mut v___y_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5393_: usize = 0;
    let mut v_i_boxed_5394_: usize = 0;
    let mut v_res_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5393_ = leanh::lean_unbox_usize(v_sz_5385_);
    leanh::lean_dec(v_sz_5385_);
    v_i_boxed_5394_ = leanh::lean_unbox_usize(v_i_5386_);
    leanh::lean_dec(v_i_5386_);
    v_res_5395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_5383_, v_as_5384_, v_sz_boxed_5393_, v_i_boxed_5394_, v_b_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
    leanh::lean_dec(v___y_5391_);
    leanh::lean_dec_ref(v___y_5390_);
    leanh::lean_dec(v___y_5389_);
    leanh::lean_dec_ref(v___y_5388_);
    leanh::lean_dec_ref(v_as_5384_);
    leanh::lean_dec(v_init_5383_);
    return v_res_5395_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(
    mut v_init_5396_: *mut leanh::LeanObject,
    mut v_n_5397_: *mut leanh::LeanObject,
    mut v_b_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
    mut v___y_5400_: *mut leanh::LeanObject,
    mut v___y_5401_: *mut leanh::LeanObject,
    mut v___y_5402_: *mut leanh::LeanObject,
    mut v___y_5403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5404_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_5396_, v_n_5397_, v_b_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
    leanh::lean_dec(v___y_5402_);
    leanh::lean_dec_ref(v___y_5401_);
    leanh::lean_dec(v___y_5400_);
    leanh::lean_dec_ref(v___y_5399_);
    leanh::lean_dec_ref(v_n_5397_);
    leanh::lean_dec(v_init_5396_);
    return v_res_5404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(
    mut v_as_5405_: *mut leanh::LeanObject,
    mut v_sz_5406_: usize,
    mut v_i_5407_: usize,
    mut v_b_5408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5415_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: usize = 0;
    let mut v___x_5422_: usize = 0;
    let mut v_reuseFailAlloc_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: u8 = 0;
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5430_: u8 = 0;
    let mut v_unused_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5410_ = lean_usize_dec_lt(v_i_5407_, v_sz_5406_);
                if v___x_5410_ == 0 {
                    v___x_5411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5411_, 0, v_b_5408_);
                    return v___x_5411_;
                } else {
                    v_snd_5412_ = leanh::lean_ctor_get(v_b_5408_, 1);
                    v_isSharedCheck_5430_ = (!leanh::lean_is_exclusive(v_b_5408_)) as u8;
                    if v_isSharedCheck_5430_ == 0 {
                        v_unused_5431_ = leanh::lean_ctor_get(v_b_5408_, 0);
                        leanh::lean_dec(v_unused_5431_);
                        v___x_5414_ = v_b_5408_;
                        v_isShared_5415_ = v_isSharedCheck_5430_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5412_);
                        leanh::lean_dec(v_b_5408_);
                        v___x_5414_ = leanh::lean_box(0);
                        v_isShared_5415_ = v_isSharedCheck_5430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5416_ = leanh::lean_box(0);
                v_a_5425_ = lean_array_uget_borrowed(v_as_5405_, v_i_5407_);
                if leanh::lean_obj_tag(v_a_5425_) == 0 {
                    v_a_5418_ = v_snd_5412_;
                    state = 2;
                    continue;
                } else {
                    v_val_5426_ = leanh::lean_ctor_get(v_a_5425_, 0);
                    v___x_5427_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5426_);
                    if v___x_5427_ == 0 {
                        v_a_5418_ = v_snd_5412_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5428_ = l_Lean_LocalDecl_fvarId(v_val_5426_);
                        v___x_5429_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5429_, 0, v___x_5428_);
                        leanh::lean_ctor_set(v___x_5429_, 1, v_snd_5412_);
                        v_a_5418_ = v___x_5429_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5415_ == 0 {
                    leanh::lean_ctor_set(v___x_5414_, 1, v_a_5418_);
                    leanh::lean_ctor_set(v___x_5414_, 0, v___x_5416_);
                    v___x_5420_ = v___x_5414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5424_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_a_5418_);
                    v___x_5420_ = v_reuseFailAlloc_5424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5421_ = 1usize;
                v___x_5422_ = lean_usize_add(v_i_5407_, v___x_5421_);
                v_i_5407_ = v___x_5422_;
                v_b_5408_ = v___x_5420_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_as_5432_: *mut leanh::LeanObject,
    mut v_sz_5433_: *mut leanh::LeanObject,
    mut v_i_5434_: *mut leanh::LeanObject,
    mut v_b_5435_: *mut leanh::LeanObject,
    mut v___y_5436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5437_: usize = 0;
    let mut v_i_boxed_5438_: usize = 0;
    let mut v_res_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5437_ = leanh::lean_unbox_usize(v_sz_5433_);
    leanh::lean_dec(v_sz_5433_);
    v_i_boxed_5438_ = leanh::lean_unbox_usize(v_i_5434_);
    leanh::lean_dec(v_i_5434_);
    v_res_5439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_5432_, v_sz_boxed_5437_, v_i_boxed_5438_, v_b_5435_);
    leanh::lean_dec_ref(v_as_5432_);
    return v_res_5439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(
    mut v_as_5440_: *mut leanh::LeanObject,
    mut v_sz_5441_: usize,
    mut v_i_5442_: usize,
    mut v_b_5443_: *mut leanh::LeanObject,
    mut v___y_5444_: *mut leanh::LeanObject,
    mut v___y_5445_: *mut leanh::LeanObject,
    mut v___y_5446_: *mut leanh::LeanObject,
    mut v___y_5447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: usize = 0;
    let mut v___x_5461_: usize = 0;
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v_unused_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5449_ = lean_usize_dec_lt(v_i_5442_, v_sz_5441_);
                if v___x_5449_ == 0 {
                    v___x_5450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5450_, 0, v_b_5443_);
                    return v___x_5450_;
                } else {
                    v_snd_5451_ = leanh::lean_ctor_get(v_b_5443_, 1);
                    v_isSharedCheck_5469_ = (!leanh::lean_is_exclusive(v_b_5443_)) as u8;
                    if v_isSharedCheck_5469_ == 0 {
                        v_unused_5470_ = leanh::lean_ctor_get(v_b_5443_, 0);
                        leanh::lean_dec(v_unused_5470_);
                        v___x_5453_ = v_b_5443_;
                        v_isShared_5454_ = v_isSharedCheck_5469_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5451_);
                        leanh::lean_dec(v_b_5443_);
                        v___x_5453_ = leanh::lean_box(0);
                        v_isShared_5454_ = v_isSharedCheck_5469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5455_ = leanh::lean_box(0);
                v_a_5464_ = lean_array_uget_borrowed(v_as_5440_, v_i_5442_);
                if leanh::lean_obj_tag(v_a_5464_) == 0 {
                    v_a_5457_ = v_snd_5451_;
                    state = 2;
                    continue;
                } else {
                    v_val_5465_ = leanh::lean_ctor_get(v_a_5464_, 0);
                    v___x_5466_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5465_);
                    if v___x_5466_ == 0 {
                        v_a_5457_ = v_snd_5451_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5467_ = l_Lean_LocalDecl_fvarId(v_val_5465_);
                        v___x_5468_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5468_, 0, v___x_5467_);
                        leanh::lean_ctor_set(v___x_5468_, 1, v_snd_5451_);
                        v_a_5457_ = v___x_5468_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5454_ == 0 {
                    leanh::lean_ctor_set(v___x_5453_, 1, v_a_5457_);
                    leanh::lean_ctor_set(v___x_5453_, 0, v___x_5455_);
                    v___x_5459_ = v___x_5453_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 1, v_a_5457_);
                    v___x_5459_ = v_reuseFailAlloc_5463_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5460_ = 1usize;
                v___x_5461_ = lean_usize_add(v_i_5442_, v___x_5460_);
                v___x_5462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_5440_, v_sz_5441_, v___x_5461_, v___x_5459_);
                return v___x_5462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(
    mut v_as_5471_: *mut leanh::LeanObject,
    mut v_sz_5472_: *mut leanh::LeanObject,
    mut v_i_5473_: *mut leanh::LeanObject,
    mut v_b_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
    mut v___y_5476_: *mut leanh::LeanObject,
    mut v___y_5477_: *mut leanh::LeanObject,
    mut v___y_5478_: *mut leanh::LeanObject,
    mut v___y_5479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5480_: usize = 0;
    let mut v_i_boxed_5481_: usize = 0;
    let mut v_res_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5480_ = leanh::lean_unbox_usize(v_sz_5472_);
    leanh::lean_dec(v_sz_5472_);
    v_i_boxed_5481_ = leanh::lean_unbox_usize(v_i_5473_);
    leanh::lean_dec(v_i_5473_);
    v_res_5482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_5471_, v_sz_boxed_5480_, v_i_boxed_5481_, v_b_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_);
    leanh::lean_dec(v___y_5478_);
    leanh::lean_dec_ref(v___y_5477_);
    leanh::lean_dec(v___y_5476_);
    leanh::lean_dec_ref(v___y_5475_);
    leanh::lean_dec_ref(v_as_5471_);
    return v_res_5482_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(
    mut v_t_5483_: *mut leanh::LeanObject,
    mut v_init_5484_: *mut leanh::LeanObject,
    mut v___y_5485_: *mut leanh::LeanObject,
    mut v___y_5486_: *mut leanh::LeanObject,
    mut v___y_5487_: *mut leanh::LeanObject,
    mut v___y_5488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v_a_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5504_: usize = 0;
    let mut v___x_5505_: usize = 0;
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v_fst_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_a_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_isSharedCheck_5529_: u8 = 0;
    let mut v_a_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5533_: u8 = 0;
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5490_ = leanh::lean_ctor_get(v_t_5483_, 0);
                v_tail_5491_ = leanh::lean_ctor_get(v_t_5483_, 1);
                leanh::lean_inc(v_init_5484_);
                v___x_5492_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_5484_, v_root_5490_, v_init_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
                leanh::lean_dec(v_init_5484_);
                if leanh::lean_obj_tag(v___x_5492_) == 0 {
                    v_a_5493_ = leanh::lean_ctor_get(v___x_5492_, 0);
                    v_isSharedCheck_5529_ = (!leanh::lean_is_exclusive(v___x_5492_)) as u8;
                    if v_isSharedCheck_5529_ == 0 {
                        v___x_5495_ = v___x_5492_;
                        v_isShared_5496_ = v_isSharedCheck_5529_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5493_);
                        leanh::lean_dec(v___x_5492_);
                        v___x_5495_ = leanh::lean_box(0);
                        v_isShared_5496_ = v_isSharedCheck_5529_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5530_ = leanh::lean_ctor_get(v___x_5492_, 0);
                    v_isSharedCheck_5537_ = (!leanh::lean_is_exclusive(v___x_5492_)) as u8;
                    if v_isSharedCheck_5537_ == 0 {
                        v___x_5532_ = v___x_5492_;
                        v_isShared_5533_ = v_isSharedCheck_5537_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5530_);
                        leanh::lean_dec(v___x_5492_);
                        v___x_5532_ = leanh::lean_box(0);
                        v_isShared_5533_ = v_isSharedCheck_5537_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5493_) == 0 {
                    v_a_5497_ = leanh::lean_ctor_get(v_a_5493_, 0);
                    leanh::lean_inc(v_a_5497_);
                    leanh::lean_dec_ref_known(v_a_5493_, 1);
                    if v_isShared_5496_ == 0 {
                        leanh::lean_ctor_set(v___x_5495_, 0, v_a_5497_);
                        v___x_5499_ = v___x_5495_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5497_);
                        v___x_5499_ = v_reuseFailAlloc_5500_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5495_);
                    v_a_5501_ = leanh::lean_ctor_get(v_a_5493_, 0);
                    leanh::lean_inc(v_a_5501_);
                    leanh::lean_dec_ref_known(v_a_5493_, 1);
                    v___x_5502_ = leanh::lean_box(0);
                    v___x_5503_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5503_, 0, v___x_5502_);
                    leanh::lean_ctor_set(v___x_5503_, 1, v_a_5501_);
                    v_sz_5504_ = lean_array_size(v_tail_5491_);
                    v___x_5505_ = 0usize;
                    v___x_5506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_5491_, v_sz_5504_, v___x_5505_, v___x_5503_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
                    if leanh::lean_obj_tag(v___x_5506_) == 0 {
                        v_a_5507_ = leanh::lean_ctor_get(v___x_5506_, 0);
                        v_isSharedCheck_5520_ =
                            (!leanh::lean_is_exclusive(v___x_5506_)) as u8;
                        if v_isSharedCheck_5520_ == 0 {
                            v___x_5509_ = v___x_5506_;
                            v_isShared_5510_ = v_isSharedCheck_5520_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5507_);
                            leanh::lean_dec(v___x_5506_);
                            v___x_5509_ = leanh::lean_box(0);
                            v_isShared_5510_ = v_isSharedCheck_5520_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5521_ = leanh::lean_ctor_get(v___x_5506_, 0);
                        v_isSharedCheck_5528_ =
                            (!leanh::lean_is_exclusive(v___x_5506_)) as u8;
                        if v_isSharedCheck_5528_ == 0 {
                            v___x_5523_ = v___x_5506_;
                            v_isShared_5524_ = v_isSharedCheck_5528_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5521_);
                            leanh::lean_dec(v___x_5506_);
                            v___x_5523_ = leanh::lean_box(0);
                            v_isShared_5524_ = v_isSharedCheck_5528_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5499_;
            }
            3 => {
                v_fst_5511_ = leanh::lean_ctor_get(v_a_5507_, 0);
                if leanh::lean_obj_tag(v_fst_5511_) == 0 {
                    v_snd_5512_ = leanh::lean_ctor_get(v_a_5507_, 1);
                    leanh::lean_inc(v_snd_5512_);
                    leanh::lean_dec(v_a_5507_);
                    if v_isShared_5510_ == 0 {
                        leanh::lean_ctor_set(v___x_5509_, 0, v_snd_5512_);
                        v___x_5514_ = v___x_5509_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_snd_5512_);
                        v___x_5514_ = v_reuseFailAlloc_5515_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5511_);
                    leanh::lean_dec(v_a_5507_);
                    v_val_5516_ = leanh::lean_ctor_get(v_fst_5511_, 0);
                    leanh::lean_inc(v_val_5516_);
                    leanh::lean_dec_ref_known(v_fst_5511_, 1);
                    if v_isShared_5510_ == 0 {
                        leanh::lean_ctor_set(v___x_5509_, 0, v_val_5516_);
                        v___x_5518_ = v___x_5509_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_val_5516_);
                        v___x_5518_ = v_reuseFailAlloc_5519_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5514_;
            }
            5 => {
                return v___x_5518_;
            }
            6 => {
                if v_isShared_5524_ == 0 {
                    v___x_5526_ = v___x_5523_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
                    v___x_5526_ = v_reuseFailAlloc_5527_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5526_;
            }
            8 => {
                if v_isShared_5533_ == 0 {
                    v___x_5535_ = v___x_5532_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
                    v___x_5535_ = v_reuseFailAlloc_5536_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(
    mut v_t_5538_: *mut leanh::LeanObject,
    mut v_init_5539_: *mut leanh::LeanObject,
    mut v___y_5540_: *mut leanh::LeanObject,
    mut v___y_5541_: *mut leanh::LeanObject,
    mut v___y_5542_: *mut leanh::LeanObject,
    mut v___y_5543_: *mut leanh::LeanObject,
    mut v___y_5544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5545_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(
        v_t_5538_,
        v_init_5539_,
        v___y_5540_,
        v___y_5541_,
        v___y_5542_,
        v___y_5543_,
    );
    leanh::lean_dec(v___y_5543_);
    leanh::lean_dec_ref(v___y_5542_);
    leanh::lean_dec(v___y_5541_);
    leanh::lean_dec_ref(v___y_5540_);
    leanh::lean_dec_ref(v_t_5538_);
    return v_res_5545_;
}
pub unsafe fn l_Lean_MVarId_clearImplDetails___lam__0(
    mut v_mvarId_5546_: *mut leanh::LeanObject,
    mut v___x_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
    mut v___y_5551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5562_: u8 = 0;
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut v_a_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v_a_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5579_: u8 = 0;
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_5546_);
                v___x_5553_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5546_,
                    v___x_5547_,
                    v___y_5548_,
                    v___y_5549_,
                    v___y_5550_,
                    v___y_5551_,
                );
                if leanh::lean_obj_tag(v___x_5553_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5553_, 1);
                    v_lctx_5554_ = leanh::lean_ctor_get(v___y_5548_, 2);
                    v_decls_5555_ = leanh::lean_ctor_get(v_lctx_5554_, 1);
                    v___x_5556_ = leanh::lean_box(0);
                    v___x_5557_ =
                        l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(
                            v_decls_5555_,
                            v___x_5556_,
                            v___y_5548_,
                            v___y_5549_,
                            v___y_5550_,
                            v___y_5551_,
                        );
                    if leanh::lean_obj_tag(v___x_5557_) == 0 {
                        v_a_5558_ = leanh::lean_ctor_get(v___x_5557_, 0);
                        v_isSharedCheck_5567_ =
                            (!leanh::lean_is_exclusive(v___x_5557_)) as u8;
                        if v_isSharedCheck_5567_ == 0 {
                            v___x_5560_ = v___x_5557_;
                            v_isShared_5561_ = v_isSharedCheck_5567_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5558_);
                            leanh::lean_dec(v___x_5557_);
                            v___x_5560_ = leanh::lean_box(0);
                            v_isShared_5561_ = v_isSharedCheck_5567_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_5546_);
                        v_a_5568_ = leanh::lean_ctor_get(v___x_5557_, 0);
                        v_isSharedCheck_5575_ =
                            (!leanh::lean_is_exclusive(v___x_5557_)) as u8;
                        if v_isSharedCheck_5575_ == 0 {
                            v___x_5570_ = v___x_5557_;
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5568_);
                            leanh::lean_dec(v___x_5557_);
                            v___x_5570_ = leanh::lean_box(0);
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_5546_);
                    v_a_5576_ = leanh::lean_ctor_get(v___x_5553_, 0);
                    v_isSharedCheck_5583_ = (!leanh::lean_is_exclusive(v___x_5553_)) as u8;
                    if v_isSharedCheck_5583_ == 0 {
                        v___x_5578_ = v___x_5553_;
                        v_isShared_5579_ = v_isSharedCheck_5583_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5576_);
                        leanh::lean_dec(v___x_5553_);
                        v___x_5578_ = leanh::lean_box(0);
                        v_isShared_5579_ = v_isSharedCheck_5583_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5562_ = l_List_isEmpty___redArg(v_a_5558_);
                if v___x_5562_ == 0 {
                    leanh::lean_del_object(v___x_5560_);
                    v___x_5563_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_5558_, v_mvarId_5546_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
                    leanh::lean_dec(v_a_5558_);
                    return v___x_5563_;
                } else {
                    leanh::lean_dec(v_a_5558_);
                    if v_isShared_5561_ == 0 {
                        leanh::lean_ctor_set(v___x_5560_, 0, v_mvarId_5546_);
                        v___x_5565_ = v___x_5560_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_mvarId_5546_);
                        v___x_5565_ = v_reuseFailAlloc_5566_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5565_;
            }
            3 => {
                if v_isShared_5571_ == 0 {
                    v___x_5573_ = v___x_5570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5573_;
            }
            5 => {
                if v_isShared_5579_ == 0 {
                    v___x_5581_ = v___x_5578_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
                    v___x_5581_ = v_reuseFailAlloc_5582_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_clearImplDetails___lam__0___boxed(
    mut v_mvarId_5584_: *mut leanh::LeanObject,
    mut v___x_5585_: *mut leanh::LeanObject,
    mut v___y_5586_: *mut leanh::LeanObject,
    mut v___y_5587_: *mut leanh::LeanObject,
    mut v___y_5588_: *mut leanh::LeanObject,
    mut v___y_5589_: *mut leanh::LeanObject,
    mut v___y_5590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5591_ = l_Lean_MVarId_clearImplDetails___lam__0(
        v_mvarId_5584_,
        v___x_5585_,
        v___y_5586_,
        v___y_5587_,
        v___y_5588_,
        v___y_5589_,
    );
    leanh::lean_dec(v___y_5589_);
    leanh::lean_dec_ref(v___y_5588_);
    leanh::lean_dec(v___y_5587_);
    leanh::lean_dec_ref(v___y_5586_);
    return v_res_5591_;
}
pub unsafe fn l_Lean_MVarId_clearImplDetails(
    mut v_mvarId_5596_: *mut leanh::LeanObject,
    mut v_a_5597_: *mut leanh::LeanObject,
    mut v_a_5598_: *mut leanh::LeanObject,
    mut v_a_5599_: *mut leanh::LeanObject,
    mut v_a_5600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5602_ = l_Lean_MVarId_clearImplDetails___closed__1;
    leanh::lean_inc(v_mvarId_5596_);
    v___f_5603_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_clearImplDetails___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_5603_, 0, v_mvarId_5596_);
    leanh::lean_closure_set(v___f_5603_, 1, v___x_5602_);
    v___x_5604_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
        v_mvarId_5596_,
        v___f_5603_,
        v_a_5597_,
        v_a_5598_,
        v_a_5599_,
        v_a_5600_,
    );
    return v___x_5604_;
}
pub unsafe fn l_Lean_MVarId_clearImplDetails___boxed(
    mut v_mvarId_5605_: *mut leanh::LeanObject,
    mut v_a_5606_: *mut leanh::LeanObject,
    mut v_a_5607_: *mut leanh::LeanObject,
    mut v_a_5608_: *mut leanh::LeanObject,
    mut v_a_5609_: *mut leanh::LeanObject,
    mut v_a_5610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5611_ =
        l_Lean_MVarId_clearImplDetails(v_mvarId_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
    leanh::lean_dec(v_a_5609_);
    leanh::lean_dec_ref(v_a_5608_);
    leanh::lean_dec(v_a_5607_);
    leanh::lean_dec_ref(v_a_5606_);
    return v_res_5611_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(
    mut v_as_5612_: *mut leanh::LeanObject,
    mut v_as_x27_5613_: *mut leanh::LeanObject,
    mut v_b_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
    mut v___y_5616_: *mut leanh::LeanObject,
    mut v___y_5617_: *mut leanh::LeanObject,
    mut v___y_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5621_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(
        v_as_x27_5613_,
        v_b_5614_,
        v___y_5616_,
        v___y_5617_,
        v___y_5618_,
        v___y_5619_,
    );
    return v___x_5621_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(
    mut v_as_5622_: *mut leanh::LeanObject,
    mut v_as_x27_5623_: *mut leanh::LeanObject,
    mut v_b_5624_: *mut leanh::LeanObject,
    mut v_a_5625_: *mut leanh::LeanObject,
    mut v___y_5626_: *mut leanh::LeanObject,
    mut v___y_5627_: *mut leanh::LeanObject,
    mut v___y_5628_: *mut leanh::LeanObject,
    mut v___y_5629_: *mut leanh::LeanObject,
    mut v___y_5630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5631_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(
        v_as_5622_,
        v_as_x27_5623_,
        v_b_5624_,
        v_a_5625_,
        v___y_5626_,
        v___y_5627_,
        v___y_5628_,
        v___y_5629_,
    );
    leanh::lean_dec(v___y_5629_);
    leanh::lean_dec_ref(v___y_5628_);
    leanh::lean_dec(v___y_5627_);
    leanh::lean_dec_ref(v___y_5626_);
    leanh::lean_dec(v_as_x27_5623_);
    leanh::lean_dec(v_as_5622_);
    return v_res_5631_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(
    mut v_as_5632_: *mut leanh::LeanObject,
    mut v_sz_5633_: usize,
    mut v_i_5634_: usize,
    mut v_b_5635_: *mut leanh::LeanObject,
    mut v___y_5636_: *mut leanh::LeanObject,
    mut v___y_5637_: *mut leanh::LeanObject,
    mut v___y_5638_: *mut leanh::LeanObject,
    mut v___y_5639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_5632_, v_sz_5633_, v_i_5634_, v_b_5635_);
    return v___x_5641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(
    mut v_as_5642_: *mut leanh::LeanObject,
    mut v_sz_5643_: *mut leanh::LeanObject,
    mut v_i_5644_: *mut leanh::LeanObject,
    mut v_b_5645_: *mut leanh::LeanObject,
    mut v___y_5646_: *mut leanh::LeanObject,
    mut v___y_5647_: *mut leanh::LeanObject,
    mut v___y_5648_: *mut leanh::LeanObject,
    mut v___y_5649_: *mut leanh::LeanObject,
    mut v___y_5650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5651_: usize = 0;
    let mut v_i_boxed_5652_: usize = 0;
    let mut v_res_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5651_ = leanh::lean_unbox_usize(v_sz_5643_);
    leanh::lean_dec(v_sz_5643_);
    v_i_boxed_5652_ = leanh::lean_unbox_usize(v_i_5644_);
    leanh::lean_dec(v_i_5644_);
    v_res_5653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_5642_, v_sz_boxed_5651_, v_i_boxed_5652_, v_b_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
    leanh::lean_dec(v___y_5649_);
    leanh::lean_dec_ref(v___y_5648_);
    leanh::lean_dec(v___y_5647_);
    leanh::lean_dec_ref(v___y_5646_);
    leanh::lean_dec_ref(v_as_5642_);
    return v_res_5653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(
    mut v_as_5654_: *mut leanh::LeanObject,
    mut v_sz_5655_: usize,
    mut v_i_5656_: usize,
    mut v_b_5657_: *mut leanh::LeanObject,
    mut v___y_5658_: *mut leanh::LeanObject,
    mut v___y_5659_: *mut leanh::LeanObject,
    mut v___y_5660_: *mut leanh::LeanObject,
    mut v___y_5661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_5654_, v_sz_5655_, v_i_5656_, v_b_5657_);
    return v___x_5663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_as_5664_: *mut leanh::LeanObject,
    mut v_sz_5665_: *mut leanh::LeanObject,
    mut v_i_5666_: *mut leanh::LeanObject,
    mut v_b_5667_: *mut leanh::LeanObject,
    mut v___y_5668_: *mut leanh::LeanObject,
    mut v___y_5669_: *mut leanh::LeanObject,
    mut v___y_5670_: *mut leanh::LeanObject,
    mut v___y_5671_: *mut leanh::LeanObject,
    mut v___y_5672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5673_: usize = 0;
    let mut v_i_boxed_5674_: usize = 0;
    let mut v_res_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5673_ = leanh::lean_unbox_usize(v_sz_5665_);
    leanh::lean_dec(v_sz_5665_);
    v_i_boxed_5674_ = leanh::lean_unbox_usize(v_i_5666_);
    leanh::lean_dec(v_i_5666_);
    v_res_5675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_5664_, v_sz_boxed_5673_, v_i_boxed_5674_, v_b_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
    leanh::lean_dec(v___y_5671_);
    leanh::lean_dec_ref(v___y_5670_);
    leanh::lean_dec(v___y_5669_);
    leanh::lean_dec_ref(v___y_5668_);
    leanh::lean_dec_ref(v_as_5664_);
    return v_res_5675_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(
    mut v_e_5676_: *mut leanh::LeanObject,
    mut v___y_5677_: *mut leanh::LeanObject,
    mut v___y_5678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_5676_) {
        8 => {
            let mut v___x_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5680_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5680_, 0, v_e_5676_);
            v___x_5681_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5681_, 0, v___x_5680_);
            return v___x_5681_;
        }
        6 => {
            let mut v___x_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5682_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5682_, 0, v_e_5676_);
            v___x_5683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5683_, 0, v___x_5682_);
            return v___x_5683_;
        }
        10 => {
            let mut v_expr_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_expr_5684_ = leanh::lean_ctor_get(v_e_5676_, 1);
            leanh::lean_inc_ref(v_expr_5684_);
            leanh::lean_dec_ref_known(v_e_5676_, 2);
            v___x_5685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5685_, 0, v_expr_5684_);
            v___x_5686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5686_, 0, v___x_5685_);
            return v___x_5686_;
        }
        _ => {
            let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5687_, 0, v_e_5676_);
            v___x_5688_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5688_, 0, v___x_5687_);
            v___x_5689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_5689_, 0, v___x_5688_);
            return v___x_5689_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(
    mut v_e_5690_: *mut leanh::LeanObject,
    mut v___y_5691_: *mut leanh::LeanObject,
    mut v___y_5692_: *mut leanh::LeanObject,
    mut v___y_5693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5694_ =
        l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_5690_, v___y_5691_, v___y_5692_);
    leanh::lean_dec(v___y_5692_);
    leanh::lean_dec_ref(v___y_5691_);
    return v_res_5694_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(
    mut v_e_5695_: *mut leanh::LeanObject,
    mut v___y_5696_: *mut leanh::LeanObject,
    mut v___y_5697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5699_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5699_, 0, v_e_5695_);
    v___x_5700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5700_, 0, v___x_5699_);
    return v___x_5700_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(
    mut v_e_5701_: *mut leanh::LeanObject,
    mut v___y_5702_: *mut leanh::LeanObject,
    mut v___y_5703_: *mut leanh::LeanObject,
    mut v___y_5704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5705_ =
        l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_5701_, v___y_5702_, v___y_5703_);
    leanh::lean_dec(v___y_5703_);
    leanh::lean_dec_ref(v___y_5702_);
    return v_res_5705_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(
    mut v_00_u03b1_5706_: *mut leanh::LeanObject,
    mut v_x_5707_: *mut leanh::LeanObject,
    mut v___y_5708_: *mut leanh::LeanObject,
    mut v___y_5709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5711_ = leanh::lean_apply_1(v_x_5707_, leanh::lean_box(0));
    v___x_5712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5712_, 0, v___x_5711_);
    return v___x_5712_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(
    mut v_00_u03b1_5713_: *mut leanh::LeanObject,
    mut v_x_5714_: *mut leanh::LeanObject,
    mut v___y_5715_: *mut leanh::LeanObject,
    mut v___y_5716_: *mut leanh::LeanObject,
    mut v___y_5717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5718_ =
        l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(
            v_00_u03b1_5713_,
            v_x_5714_,
            v___y_5715_,
            v___y_5716_,
        );
    leanh::lean_dec(v___y_5716_);
    leanh::lean_dec_ref(v___y_5715_);
    return v_res_5718_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_5719_: *mut leanh::LeanObject,
    mut v_x_5720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5720_) == 0 {
                    v___x_5721_ = leanh::lean_box(0);
                    return v___x_5721_;
                } else {
                    v_key_5722_ = leanh::lean_ctor_get(v_x_5720_, 0);
                    v_value_5723_ = leanh::lean_ctor_get(v_x_5720_, 1);
                    v_tail_5724_ = leanh::lean_ctor_get(v_x_5720_, 2);
                    v___x_5725_ = l_Lean_ExprStructEq_beq(v_key_5722_, v_a_5719_);
                    if v___x_5725_ == 0 {
                        v_x_5720_ = v_tail_5724_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_5723_);
                        v___x_5727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5727_, 0, v_value_5723_);
                        return v___x_5727_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_5728_: *mut leanh::LeanObject,
    mut v_x_5729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5730_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_5728_, v_x_5729_);
    leanh::lean_dec(v_x_5729_);
    leanh::lean_dec_ref(v_a_5728_);
    return v_res_5730_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(
    mut v_m_5731_: *mut leanh::LeanObject,
    mut v_a_5732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u64 = 0;
    let mut v___x_5736_: u64 = 0;
    let mut v___x_5737_: u64 = 0;
    let mut v_fold_5738_: u64 = 0;
    let mut v___x_5739_: u64 = 0;
    let mut v___x_5740_: u64 = 0;
    let mut v___x_5741_: u64 = 0;
    let mut v___x_5742_: usize = 0;
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5745_: usize = 0;
    let mut v___x_5746_: usize = 0;
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5733_ = leanh::lean_ctor_get(v_m_5731_, 1);
    v___x_5734_ = lean_array_get_size(v_buckets_5733_);
    v___x_5735_ = l_Lean_ExprStructEq_hash(v_a_5732_);
    v___x_5736_ = 32u64;
    v___x_5737_ = lean_uint64_shift_right(v___x_5735_, v___x_5736_);
    v_fold_5738_ = lean_uint64_xor(v___x_5735_, v___x_5737_);
    v___x_5739_ = 16u64;
    v___x_5740_ = lean_uint64_shift_right(v_fold_5738_, v___x_5739_);
    v___x_5741_ = lean_uint64_xor(v_fold_5738_, v___x_5740_);
    v___x_5742_ = lean_uint64_to_usize(v___x_5741_);
    v___x_5743_ = lean_usize_of_nat(v___x_5734_);
    v___x_5744_ = 1usize;
    v___x_5745_ = lean_usize_sub(v___x_5743_, v___x_5744_);
    v___x_5746_ = lean_usize_land(v___x_5742_, v___x_5745_);
    v___x_5747_ = lean_array_uget_borrowed(v_buckets_5733_, v___x_5746_);
    v___x_5748_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_5732_, v___x_5747_);
    return v___x_5748_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_m_5749_: *mut leanh::LeanObject,
    mut v_a_5750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_5749_, v_a_5750_);
    leanh::lean_dec_ref(v_a_5750_);
    leanh::lean_dec_ref(v_m_5749_);
    return v_res_5751_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(
    mut v_00_u03b1_5752_: *mut leanh::LeanObject,
    mut v_x_5753_: *mut leanh::LeanObject,
    mut v___y_5754_: *mut leanh::LeanObject,
    mut v___y_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5757_ = leanh::lean_apply_1(v_x_5753_, leanh::lean_box(0));
    v___x_5758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_5759_: *mut leanh::LeanObject,
    mut v_x_5760_: *mut leanh::LeanObject,
    mut v___y_5761_: *mut leanh::LeanObject,
    mut v___y_5762_: *mut leanh::LeanObject,
    mut v___y_5763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5764_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_5759_, v_x_5760_, v___y_5761_, v___y_5762_);
    leanh::lean_dec(v___y_5762_);
    leanh::lean_dec_ref(v___y_5761_);
    return v_res_5764_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = leanh::lean_box(0);
    v___x_5766_ = l_Lean_interruptExceptionId;
    v___x_5767_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5767_, 0, v___x_5766_);
    leanh::lean_ctor_set(v___x_5767_, 1, v___x_5765_);
    return v___x_5767_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_5770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5770_, 0, v___x_5769_);
    return v___x_5770_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_5771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5772_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_5772_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5778_ = l_Lean_maxRecDepthErrorMessage;
    v___x_5779_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
    return v___x_5779_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5780_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_5781_ = l_Lean_MessageData_ofFormat(v___x_5780_);
    return v___x_5781_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5782_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_5783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_5784_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5784_, 0, v___x_5783_);
    leanh::lean_ctor_set(v___x_5784_, 1, v___x_5782_);
    return v___x_5784_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_5785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_5788_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5788_, 0, v_ref_5785_);
    leanh::lean_ctor_set(v___x_5788_, 1, v___x_5787_);
    v___x_5789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5789_, 0, v___x_5788_);
    return v___x_5789_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_5790_: *mut leanh::LeanObject,
    mut v___y_5791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5792_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_5790_);
    return v_res_5792_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(
    mut v_x_5793_: *mut leanh::LeanObject,
    mut v___y_5794_: *mut leanh::LeanObject,
    mut v___y_5795_: *mut leanh::LeanObject,
    mut v___y_5796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v___y_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: u8 = 0;
    let mut v___y_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5812_: u8 = 0;
    let mut v___y_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5841_: u8 = 0;
    let mut v_cancelTk_x3f_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5843_: u8 = 0;
    let mut v_inheritedTraceOptions_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: u8 = 0;
    let mut v___x_5848_: u8 = 0;
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: u8 = 0;
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5829_ = leanh::lean_ctor_get(v___y_5795_, 0);
                v_fileMap_5830_ = leanh::lean_ctor_get(v___y_5795_, 1);
                v_options_5831_ = leanh::lean_ctor_get(v___y_5795_, 2);
                v_currRecDepth_5832_ = leanh::lean_ctor_get(v___y_5795_, 3);
                v_maxRecDepth_5833_ = leanh::lean_ctor_get(v___y_5795_, 4);
                v_ref_5834_ = leanh::lean_ctor_get(v___y_5795_, 5);
                v_currNamespace_5835_ = leanh::lean_ctor_get(v___y_5795_, 6);
                v_openDecls_5836_ = leanh::lean_ctor_get(v___y_5795_, 7);
                v_initHeartbeats_5837_ = leanh::lean_ctor_get(v___y_5795_, 8);
                v_maxHeartbeats_5838_ = leanh::lean_ctor_get(v___y_5795_, 9);
                v_quotContext_5839_ = leanh::lean_ctor_get(v___y_5795_, 10);
                v_currMacroScope_5840_ = leanh::lean_ctor_get(v___y_5795_, 11);
                v_diag_5841_ = leanh::lean_ctor_get_uint8(
                    v___y_5795_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5842_ = leanh::lean_ctor_get(v___y_5795_, 12);
                v_suppressElabErrors_5843_ = leanh::lean_ctor_get_uint8(
                    v___y_5795_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5844_ = leanh::lean_ctor_get(v___y_5795_, 13);
                if leanh::lean_obj_tag(v_cancelTk_x3f_5842_) == 1 {
                    v_val_5850_ = leanh::lean_ctor_get(v_cancelTk_x3f_5842_, 0);
                    v___x_5851_ = l_IO_CancelToken_isSet(v_val_5850_);
                    if v___x_5851_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_5793_);
                        v___x_5852_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_5853_ = leanh::lean_ctor_get(v___x_5852_, 0);
                        v_isSharedCheck_5860_ =
                            (!leanh::lean_is_exclusive(v___x_5852_)) as u8;
                        if v_isSharedCheck_5860_ == 0 {
                            v___x_5855_ = v___x_5852_;
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5853_);
                            leanh::lean_dec(v___x_5852_);
                            v___x_5855_ = leanh::lean_box(0);
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_5799_) == 0 {
                    return v___y_5799_;
                } else {
                    v_a_5800_ = leanh::lean_ctor_get(v___y_5799_, 0);
                    v_isSharedCheck_5807_ = (!leanh::lean_is_exclusive(v___y_5799_)) as u8;
                    if v_isSharedCheck_5807_ == 0 {
                        v___x_5802_ = v___y_5799_;
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5800_);
                        leanh::lean_dec(v___y_5799_);
                        v___x_5802_ = leanh::lean_box(0);
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5803_ == 0 {
                    v___x_5805_ = v___x_5802_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
                    v___x_5805_ = v_reuseFailAlloc_5806_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5805_;
            }
            4 => {
                v___x_5825_ = leanh::lean_unsigned_to_nat(1);
                v___x_5826_ = lean_nat_add(v___y_5814_, v___x_5825_);
                leanh::lean_inc_ref(v___y_5821_);
                leanh::lean_inc(v___y_5813_);
                leanh::lean_inc(v___y_5817_);
                leanh::lean_inc(v___y_5824_);
                leanh::lean_inc(v___y_5823_);
                leanh::lean_inc(v___y_5815_);
                leanh::lean_inc(v___y_5820_);
                leanh::lean_inc(v___y_5816_);
                leanh::lean_inc(v___y_5811_);
                leanh::lean_inc_ref(v___y_5809_);
                leanh::lean_inc_ref(v___y_5818_);
                leanh::lean_inc_ref(v___y_5819_);
                v___x_5827_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_5827_, 0, v___y_5819_);
                leanh::lean_ctor_set(v___x_5827_, 1, v___y_5818_);
                leanh::lean_ctor_set(v___x_5827_, 2, v___y_5809_);
                leanh::lean_ctor_set(v___x_5827_, 3, v___x_5826_);
                leanh::lean_ctor_set(v___x_5827_, 4, v___y_5811_);
                leanh::lean_ctor_set(v___x_5827_, 5, v___y_5822_);
                leanh::lean_ctor_set(v___x_5827_, 6, v___y_5816_);
                leanh::lean_ctor_set(v___x_5827_, 7, v___y_5820_);
                leanh::lean_ctor_set(v___x_5827_, 8, v___y_5815_);
                leanh::lean_ctor_set(v___x_5827_, 9, v___y_5823_);
                leanh::lean_ctor_set(v___x_5827_, 10, v___y_5824_);
                leanh::lean_ctor_set(v___x_5827_, 11, v___y_5817_);
                leanh::lean_ctor_set(v___x_5827_, 12, v___y_5813_);
                leanh::lean_ctor_set(v___x_5827_, 13, v___y_5821_);
                leanh::lean_ctor_set_uint8(
                    v___x_5827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_5812_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_5810_,
                );
                leanh::lean_inc(v___y_5796_);
                leanh::lean_inc(v___y_5794_);
                v___x_5828_ = leanh::lean_apply_4(
                    v_x_5793_,
                    v___y_5794_,
                    v___x_5827_,
                    v___y_5796_,
                    leanh::lean_box(0),
                );
                v___y_5799_ = v___x_5828_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5846_ = leanh::lean_unsigned_to_nat(0);
                v___x_5847_ = lean_nat_dec_eq(v_maxRecDepth_5833_, v___x_5846_);
                if v___x_5847_ == 0 {
                    v___x_5848_ = lean_nat_dec_eq(v_currRecDepth_5832_, v_maxRecDepth_5833_);
                    if v___x_5848_ == 0 {
                        leanh::lean_inc(v_ref_5834_);
                        v___y_5809_ = v_options_5831_;
                        v___y_5810_ = v_suppressElabErrors_5843_;
                        v___y_5811_ = v_maxRecDepth_5833_;
                        v___y_5812_ = v_diag_5841_;
                        v___y_5813_ = v_cancelTk_x3f_5842_;
                        v___y_5814_ = v_currRecDepth_5832_;
                        v___y_5815_ = v_initHeartbeats_5837_;
                        v___y_5816_ = v_currNamespace_5835_;
                        v___y_5817_ = v_currMacroScope_5840_;
                        v___y_5818_ = v_fileMap_5830_;
                        v___y_5819_ = v_fileName_5829_;
                        v___y_5820_ = v_openDecls_5836_;
                        v___y_5821_ = v_inheritedTraceOptions_5844_;
                        v___y_5822_ = v_ref_5834_;
                        v___y_5823_ = v_maxHeartbeats_5838_;
                        v___y_5824_ = v_quotContext_5839_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_5793_);
                        leanh::lean_inc(v_ref_5834_);
                        v___x_5849_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_5834_);
                        v___y_5799_ = v___x_5849_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_ref_5834_);
                    v___y_5809_ = v_options_5831_;
                    v___y_5810_ = v_suppressElabErrors_5843_;
                    v___y_5811_ = v_maxRecDepth_5833_;
                    v___y_5812_ = v_diag_5841_;
                    v___y_5813_ = v_cancelTk_x3f_5842_;
                    v___y_5814_ = v_currRecDepth_5832_;
                    v___y_5815_ = v_initHeartbeats_5837_;
                    v___y_5816_ = v_currNamespace_5835_;
                    v___y_5817_ = v_currMacroScope_5840_;
                    v___y_5818_ = v_fileMap_5830_;
                    v___y_5819_ = v_fileName_5829_;
                    v___y_5820_ = v_openDecls_5836_;
                    v___y_5821_ = v_inheritedTraceOptions_5844_;
                    v___y_5822_ = v_ref_5834_;
                    v___y_5823_ = v_maxHeartbeats_5838_;
                    v___y_5824_ = v_quotContext_5839_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_5856_ == 0 {
                    v___x_5858_ = v___x_5855_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
                    v___x_5858_ = v_reuseFailAlloc_5859_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(
    mut v_x_5861_: *mut leanh::LeanObject,
    mut v___y_5862_: *mut leanh::LeanObject,
    mut v___y_5863_: *mut leanh::LeanObject,
    mut v___y_5864_: *mut leanh::LeanObject,
    mut v___y_5865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_5861_, v___y_5862_, v___y_5863_, v___y_5864_);
    leanh::lean_dec(v___y_5864_);
    leanh::lean_dec_ref(v___y_5863_);
    leanh::lean_dec(v___y_5862_);
    return v_res_5866_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(
    mut v_x_5867_: *mut leanh::LeanObject,
    mut v_x_5868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: u64 = 0;
    let mut v___x_5877_: u64 = 0;
    let mut v___x_5878_: u64 = 0;
    let mut v_fold_5879_: u64 = 0;
    let mut v___x_5880_: u64 = 0;
    let mut v___x_5881_: u64 = 0;
    let mut v___x_5882_: u64 = 0;
    let mut v___x_5883_: usize = 0;
    let mut v___x_5884_: usize = 0;
    let mut v___x_5885_: usize = 0;
    let mut v___x_5886_: usize = 0;
    let mut v___x_5887_: usize = 0;
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5868_) == 0 {
                    return v_x_5867_;
                } else {
                    v_key_5869_ = leanh::lean_ctor_get(v_x_5868_, 0);
                    v_value_5870_ = leanh::lean_ctor_get(v_x_5868_, 1);
                    v_tail_5871_ = leanh::lean_ctor_get(v_x_5868_, 2);
                    v_isSharedCheck_5894_ = (!leanh::lean_is_exclusive(v_x_5868_)) as u8;
                    if v_isSharedCheck_5894_ == 0 {
                        v___x_5873_ = v_x_5868_;
                        v_isShared_5874_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5871_);
                        leanh::lean_inc(v_value_5870_);
                        leanh::lean_inc(v_key_5869_);
                        leanh::lean_dec(v_x_5868_);
                        v___x_5873_ = leanh::lean_box(0);
                        v_isShared_5874_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5875_ = lean_array_get_size(v_x_5867_);
                v___x_5876_ = l_Lean_ExprStructEq_hash(v_key_5869_);
                v___x_5877_ = 32u64;
                v___x_5878_ = lean_uint64_shift_right(v___x_5876_, v___x_5877_);
                v_fold_5879_ = lean_uint64_xor(v___x_5876_, v___x_5878_);
                v___x_5880_ = 16u64;
                v___x_5881_ = lean_uint64_shift_right(v_fold_5879_, v___x_5880_);
                v___x_5882_ = lean_uint64_xor(v_fold_5879_, v___x_5881_);
                v___x_5883_ = lean_uint64_to_usize(v___x_5882_);
                v___x_5884_ = lean_usize_of_nat(v___x_5875_);
                v___x_5885_ = 1usize;
                v___x_5886_ = lean_usize_sub(v___x_5884_, v___x_5885_);
                v___x_5887_ = lean_usize_land(v___x_5883_, v___x_5886_);
                v___x_5888_ = lean_array_uget_borrowed(v_x_5867_, v___x_5887_);
                leanh::lean_inc(v___x_5888_);
                if v_isShared_5874_ == 0 {
                    leanh::lean_ctor_set(v___x_5873_, 2, v___x_5888_);
                    v___x_5890_ = v___x_5873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_key_5869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 1, v_value_5870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 2, v___x_5888_);
                    v___x_5890_ = v_reuseFailAlloc_5893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5891_ = lean_array_uset(v_x_5867_, v___x_5887_, v___x_5890_);
                v_x_5867_ = v___x_5891_;
                v_x_5868_ = v_tail_5871_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(
    mut v_i_5895_: *mut leanh::LeanObject,
    mut v_source_5896_: *mut leanh::LeanObject,
    mut v_target_5897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    let mut v_es_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5898_ = lean_array_get_size(v_source_5896_);
                v___x_5899_ = lean_nat_dec_lt(v_i_5895_, v___x_5898_);
                if v___x_5899_ == 0 {
                    leanh::lean_dec_ref(v_source_5896_);
                    leanh::lean_dec(v_i_5895_);
                    return v_target_5897_;
                } else {
                    v_es_5900_ = lean_array_fget(v_source_5896_, v_i_5895_);
                    v___x_5901_ = leanh::lean_box(0);
                    v_source_5902_ = lean_array_fset(v_source_5896_, v_i_5895_, v___x_5901_);
                    v_target_5903_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_5897_, v_es_5900_);
                    v___x_5904_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5905_ = lean_nat_add(v_i_5895_, v___x_5904_);
                    leanh::lean_dec(v_i_5895_);
                    v_i_5895_ = v___x_5905_;
                    v_source_5896_ = v_source_5902_;
                    v_target_5897_ = v_target_5903_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(
    mut v_data_5907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5908_ = lean_array_get_size(v_data_5907_);
    v___x_5909_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5910_ = lean_nat_mul(v___x_5908_, v___x_5909_);
    v___x_5911_ = leanh::lean_unsigned_to_nat(0);
    v___x_5912_ = leanh::lean_box(0);
    v___x_5913_ = lean_mk_array(v_nbuckets_5910_, v___x_5912_);
    v___x_5914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_5911_, v_data_5907_, v___x_5913_);
    return v___x_5914_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_5915_: *mut leanh::LeanObject,
    mut v_b_5916_: *mut leanh::LeanObject,
    mut v_x_5917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5923_: u8 = 0;
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5917_) == 0 {
                    leanh::lean_dec(v_b_5916_);
                    leanh::lean_dec_ref(v_a_5915_);
                    return v_x_5917_;
                } else {
                    v_key_5918_ = leanh::lean_ctor_get(v_x_5917_, 0);
                    v_value_5919_ = leanh::lean_ctor_get(v_x_5917_, 1);
                    v_tail_5920_ = leanh::lean_ctor_get(v_x_5917_, 2);
                    v_isSharedCheck_5932_ = (!leanh::lean_is_exclusive(v_x_5917_)) as u8;
                    if v_isSharedCheck_5932_ == 0 {
                        v___x_5922_ = v_x_5917_;
                        v_isShared_5923_ = v_isSharedCheck_5932_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5920_);
                        leanh::lean_inc(v_value_5919_);
                        leanh::lean_inc(v_key_5918_);
                        leanh::lean_dec(v_x_5917_);
                        v___x_5922_ = leanh::lean_box(0);
                        v_isShared_5923_ = v_isSharedCheck_5932_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5924_ = l_Lean_ExprStructEq_beq(v_key_5918_, v_a_5915_);
                if v___x_5924_ == 0 {
                    v___x_5925_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_5915_, v_b_5916_, v_tail_5920_);
                    if v_isShared_5923_ == 0 {
                        leanh::lean_ctor_set(v___x_5922_, 2, v___x_5925_);
                        v___x_5927_ = v___x_5922_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5928_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5928_, 0, v_key_5918_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5928_, 1, v_value_5919_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5928_, 2, v___x_5925_);
                        v___x_5927_ = v_reuseFailAlloc_5928_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_5919_);
                    leanh::lean_dec(v_key_5918_);
                    if v_isShared_5923_ == 0 {
                        leanh::lean_ctor_set(v___x_5922_, 1, v_b_5916_);
                        leanh::lean_ctor_set(v___x_5922_, 0, v_a_5915_);
                        v___x_5930_ = v___x_5922_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5931_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5915_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_b_5916_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 2, v_tail_5920_);
                        v___x_5930_ = v_reuseFailAlloc_5931_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5927_;
            }
            3 => {
                return v___x_5930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(
    mut v_a_5933_: *mut leanh::LeanObject,
    mut v_x_5934_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5935_: u8 = 0;
    let mut v_key_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5934_) == 0 {
                    v___x_5935_ = 0;
                    return v___x_5935_;
                } else {
                    v_key_5936_ = leanh::lean_ctor_get(v_x_5934_, 0);
                    v_tail_5937_ = leanh::lean_ctor_get(v_x_5934_, 2);
                    v___x_5938_ = l_Lean_ExprStructEq_beq(v_key_5936_, v_a_5933_);
                    if v___x_5938_ == 0 {
                        v_x_5934_ = v_tail_5937_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5938_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg___boxed(
    mut v_a_5940_: *mut leanh::LeanObject,
    mut v_x_5941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5942_: u8 = 0;
    let mut v_r_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_5940_, v_x_5941_);
    leanh::lean_dec(v_x_5941_);
    leanh::lean_dec_ref(v_a_5940_);
    v_r_5943_ = leanh::lean_box((v_res_5942_) as usize);
    return v_r_5943_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(
    mut v_m_5944_: *mut leanh::LeanObject,
    mut v_a_5945_: *mut leanh::LeanObject,
    mut v_b_5946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5951_: u8 = 0;
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: u64 = 0;
    let mut v___x_5954_: u64 = 0;
    let mut v___x_5955_: u64 = 0;
    let mut v_fold_5956_: u64 = 0;
    let mut v___x_5957_: u64 = 0;
    let mut v___x_5958_: u64 = 0;
    let mut v___x_5959_: u64 = 0;
    let mut v___x_5960_: usize = 0;
    let mut v___x_5961_: usize = 0;
    let mut v___x_5962_: usize = 0;
    let mut v___x_5963_: usize = 0;
    let mut v___x_5964_: usize = 0;
    let mut v_bkt_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: u8 = 0;
    let mut v___x_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: u8 = 0;
    let mut v_val_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5947_ = leanh::lean_ctor_get(v_m_5944_, 0);
                v_buckets_5948_ = leanh::lean_ctor_get(v_m_5944_, 1);
                v_isSharedCheck_5991_ = (!leanh::lean_is_exclusive(v_m_5944_)) as u8;
                if v_isSharedCheck_5991_ == 0 {
                    v___x_5950_ = v_m_5944_;
                    v_isShared_5951_ = v_isSharedCheck_5991_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_5948_);
                    leanh::lean_inc(v_size_5947_);
                    leanh::lean_dec(v_m_5944_);
                    v___x_5950_ = leanh::lean_box(0);
                    v_isShared_5951_ = v_isSharedCheck_5991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5952_ = lean_array_get_size(v_buckets_5948_);
                v___x_5953_ = l_Lean_ExprStructEq_hash(v_a_5945_);
                v___x_5954_ = 32u64;
                v___x_5955_ = lean_uint64_shift_right(v___x_5953_, v___x_5954_);
                v_fold_5956_ = lean_uint64_xor(v___x_5953_, v___x_5955_);
                v___x_5957_ = 16u64;
                v___x_5958_ = lean_uint64_shift_right(v_fold_5956_, v___x_5957_);
                v___x_5959_ = lean_uint64_xor(v_fold_5956_, v___x_5958_);
                v___x_5960_ = lean_uint64_to_usize(v___x_5959_);
                v___x_5961_ = lean_usize_of_nat(v___x_5952_);
                v___x_5962_ = 1usize;
                v___x_5963_ = lean_usize_sub(v___x_5961_, v___x_5962_);
                v___x_5964_ = lean_usize_land(v___x_5960_, v___x_5963_);
                v_bkt_5965_ = lean_array_uget_borrowed(v_buckets_5948_, v___x_5964_);
                v___x_5966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_5945_, v_bkt_5965_);
                if v___x_5966_ == 0 {
                    v___x_5967_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5968_ = lean_nat_add(v_size_5947_, v___x_5967_);
                    leanh::lean_dec(v_size_5947_);
                    leanh::lean_inc(v_bkt_5965_);
                    v___x_5969_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5969_, 0, v_a_5945_);
                    leanh::lean_ctor_set(v___x_5969_, 1, v_b_5946_);
                    leanh::lean_ctor_set(v___x_5969_, 2, v_bkt_5965_);
                    v_buckets_x27_5970_ =
                        lean_array_uset(v_buckets_5948_, v___x_5964_, v___x_5969_);
                    v___x_5971_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5972_ = lean_nat_mul(v_size_x27_5968_, v___x_5971_);
                    v___x_5973_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5974_ = lean_nat_div(v___x_5972_, v___x_5973_);
                    leanh::lean_dec(v___x_5972_);
                    v___x_5975_ = lean_array_get_size(v_buckets_x27_5970_);
                    v___x_5976_ = lean_nat_dec_le(v___x_5974_, v___x_5975_);
                    leanh::lean_dec(v___x_5974_);
                    if v___x_5976_ == 0 {
                        v_val_5977_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_5970_);
                        if v_isShared_5951_ == 0 {
                            leanh::lean_ctor_set(v___x_5950_, 1, v_val_5977_);
                            leanh::lean_ctor_set(v___x_5950_, 0, v_size_x27_5968_);
                            v___x_5979_ = v___x_5950_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5980_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5980_,
                                0,
                                v_size_x27_5968_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 1, v_val_5977_);
                            v___x_5979_ = v_reuseFailAlloc_5980_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5951_ == 0 {
                            leanh::lean_ctor_set(v___x_5950_, 1, v_buckets_x27_5970_);
                            leanh::lean_ctor_set(v___x_5950_, 0, v_size_x27_5968_);
                            v___x_5982_ = v___x_5950_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5983_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5983_,
                                0,
                                v_size_x27_5968_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5983_,
                                1,
                                v_buckets_x27_5970_,
                            );
                            v___x_5982_ = v_reuseFailAlloc_5983_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_5965_);
                    v___x_5984_ = leanh::lean_box(0);
                    v_buckets_x27_5985_ =
                        lean_array_uset(v_buckets_5948_, v___x_5964_, v___x_5984_);
                    v___x_5986_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_5945_, v_b_5946_, v_bkt_5965_);
                    v___x_5987_ = lean_array_uset(v_buckets_x27_5985_, v___x_5964_, v___x_5986_);
                    if v_isShared_5951_ == 0 {
                        leanh::lean_ctor_set(v___x_5950_, 1, v___x_5987_);
                        v___x_5989_ = v___x_5950_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_size_5947_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5987_);
                        v___x_5989_ = v_reuseFailAlloc_5990_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5979_;
            }
            3 => {
                return v___x_5982_;
            }
            4 => {
                return v___x_5989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(
    mut v_a_5992_: *mut leanh::LeanObject,
    mut v_e_5993_: *mut leanh::LeanObject,
    mut v_a_5994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5996_ = lean_st_ref_take(v_a_5992_);
    v___x_5997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_5996_, v_e_5993_, v_a_5994_);
    v___x_5998_ = lean_st_ref_set(v_a_5992_, v___x_5997_);
    v___x_5999_ = leanh::lean_box(0);
    return v___x_5999_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(
    mut v_a_6000_: *mut leanh::LeanObject,
    mut v_e_6001_: *mut leanh::LeanObject,
    mut v_a_6002_: *mut leanh::LeanObject,
    mut v___y_6003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6004_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_6000_, v_e_6001_, v_a_6002_);
    leanh::lean_dec(v_a_6000_);
    return v_res_6004_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6006_ = leanh::lean_box(0);
    v_dummy_6007_ = l_Lean_Expr_sort___override(v___x_6006_);
    return v_dummy_6007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(
    mut v_pre_6008_: *mut leanh::LeanObject,
    mut v_post_6009_: *mut leanh::LeanObject,
    mut v_sz_6010_: usize,
    mut v_i_6011_: usize,
    mut v_bs_6012_: *mut leanh::LeanObject,
    mut v___y_6013_: *mut leanh::LeanObject,
    mut v___y_6014_: *mut leanh::LeanObject,
    mut v___y_6015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: usize = 0;
    let mut v___x_6025_: usize = 0;
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6031_: u8 = 0;
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6017_ = lean_usize_dec_lt(v_i_6011_, v_sz_6010_);
                if v___x_6017_ == 0 {
                    leanh::lean_dec_ref(v_post_6009_);
                    leanh::lean_dec_ref(v_pre_6008_);
                    v___x_6018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6018_, 0, v_bs_6012_);
                    return v___x_6018_;
                } else {
                    v_v_6019_ = lean_array_uget_borrowed(v_bs_6012_, v_i_6011_);
                    leanh::lean_inc(v_v_6019_);
                    leanh::lean_inc_ref(v_post_6009_);
                    leanh::lean_inc_ref(v_pre_6008_);
                    v___x_6020_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6008_, v_post_6009_, v_v_6019_, v___y_6013_, v___y_6014_, v___y_6015_);
                    if leanh::lean_obj_tag(v___x_6020_) == 0 {
                        v_a_6021_ = leanh::lean_ctor_get(v___x_6020_, 0);
                        leanh::lean_inc(v_a_6021_);
                        leanh::lean_dec_ref_known(v___x_6020_, 1);
                        v___x_6022_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6023_ = lean_array_uset(v_bs_6012_, v_i_6011_, v___x_6022_);
                        v___x_6024_ = 1usize;
                        v___x_6025_ = lean_usize_add(v_i_6011_, v___x_6024_);
                        v___x_6026_ = lean_array_uset(v_bs_x27_6023_, v_i_6011_, v_a_6021_);
                        v_i_6011_ = v___x_6025_;
                        v_bs_6012_ = v___x_6026_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_6012_);
                        leanh::lean_dec_ref(v_post_6009_);
                        leanh::lean_dec_ref(v_pre_6008_);
                        v_a_6028_ = leanh::lean_ctor_get(v___x_6020_, 0);
                        v_isSharedCheck_6035_ =
                            (!leanh::lean_is_exclusive(v___x_6020_)) as u8;
                        if v_isSharedCheck_6035_ == 0 {
                            v___x_6030_ = v___x_6020_;
                            v_isShared_6031_ = v_isSharedCheck_6035_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6028_);
                            leanh::lean_dec(v___x_6020_);
                            v___x_6030_ = leanh::lean_box(0);
                            v_isShared_6031_ = v_isSharedCheck_6035_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6031_ == 0 {
                    v___x_6033_ = v___x_6030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_a_6028_);
                    v___x_6033_ = v_reuseFailAlloc_6034_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(
    mut v_pre_6036_: *mut leanh::LeanObject,
    mut v_post_6037_: *mut leanh::LeanObject,
    mut v_x_6038_: *mut leanh::LeanObject,
    mut v_x_6039_: *mut leanh::LeanObject,
    mut v_x_6040_: *mut leanh::LeanObject,
    mut v___y_6041_: *mut leanh::LeanObject,
    mut v___y_6042_: *mut leanh::LeanObject,
    mut v___y_6043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6053_: usize = 0;
    let mut v___x_6054_: usize = 0;
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6062_: u8 = 0;
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6038_) == 5 {
                    v_fn_6045_ = leanh::lean_ctor_get(v_x_6038_, 0);
                    leanh::lean_inc_ref(v_fn_6045_);
                    v_arg_6046_ = leanh::lean_ctor_get(v_x_6038_, 1);
                    leanh::lean_inc_ref(v_arg_6046_);
                    leanh::lean_dec_ref_known(v_x_6038_, 2);
                    v___x_6047_ = lean_array_set(v_x_6039_, v_x_6040_, v_arg_6046_);
                    v___x_6048_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6049_ = lean_nat_sub(v_x_6040_, v___x_6048_);
                    leanh::lean_dec(v_x_6040_);
                    v_x_6038_ = v_fn_6045_;
                    v_x_6039_ = v___x_6047_;
                    v_x_6040_ = v___x_6049_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_6040_);
                    leanh::lean_inc_ref(v_post_6037_);
                    leanh::lean_inc_ref(v_pre_6036_);
                    v___x_6051_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6036_, v_post_6037_, v_x_6038_, v___y_6041_, v___y_6042_, v___y_6043_);
                    if leanh::lean_obj_tag(v___x_6051_) == 0 {
                        v_a_6052_ = leanh::lean_ctor_get(v___x_6051_, 0);
                        leanh::lean_inc(v_a_6052_);
                        leanh::lean_dec_ref_known(v___x_6051_, 1);
                        v_sz_6053_ = lean_array_size(v_x_6039_);
                        v___x_6054_ = 0usize;
                        leanh::lean_inc_ref(v_post_6037_);
                        leanh::lean_inc_ref(v_pre_6036_);
                        v___x_6055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_6036_, v_post_6037_, v_sz_6053_, v___x_6054_, v_x_6039_, v___y_6041_, v___y_6042_, v___y_6043_);
                        if leanh::lean_obj_tag(v___x_6055_) == 0 {
                            v_a_6056_ = leanh::lean_ctor_get(v___x_6055_, 0);
                            leanh::lean_inc(v_a_6056_);
                            leanh::lean_dec_ref_known(v___x_6055_, 1);
                            v___x_6057_ = l_Lean_mkAppN(v_a_6052_, v_a_6056_);
                            leanh::lean_dec(v_a_6056_);
                            v___x_6058_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6036_, v_post_6037_, v___x_6057_, v___y_6041_, v___y_6042_, v___y_6043_);
                            return v___x_6058_;
                        } else {
                            leanh::lean_dec(v_a_6052_);
                            leanh::lean_dec_ref(v_post_6037_);
                            leanh::lean_dec_ref(v_pre_6036_);
                            v_a_6059_ = leanh::lean_ctor_get(v___x_6055_, 0);
                            v_isSharedCheck_6066_ =
                                (!leanh::lean_is_exclusive(v___x_6055_)) as u8;
                            if v_isSharedCheck_6066_ == 0 {
                                v___x_6061_ = v___x_6055_;
                                v_isShared_6062_ = v_isSharedCheck_6066_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6059_);
                                leanh::lean_dec(v___x_6055_);
                                v___x_6061_ = leanh::lean_box(0);
                                v_isShared_6062_ = v_isSharedCheck_6066_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_6039_);
                        leanh::lean_dec_ref(v_post_6037_);
                        leanh::lean_dec_ref(v_pre_6036_);
                        return v___x_6051_;
                    }
                }
            }
            1 => {
                if v_isShared_6062_ == 0 {
                    v___x_6064_ = v___x_6061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
                    v___x_6064_ = v_reuseFailAlloc_6065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(
    mut v___x_6067_: *mut leanh::LeanObject,
    mut v_pre_6068_: *mut leanh::LeanObject,
    mut v_e_6069_: *mut leanh::LeanObject,
    mut v_post_6070_: *mut leanh::LeanObject,
    mut v___y_6071_: *mut leanh::LeanObject,
    mut v___y_6072_: *mut leanh::LeanObject,
    mut v___y_6073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6081_: u8 = 0;
    let mut v___y_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6083_: u8 = 0;
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: usize = 0;
    let mut v___x_6087_: usize = 0;
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: u8 = 0;
    let mut v___y_6098_: u8 = 0;
    let mut v___x_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: u8 = 0;
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: u8 = 0;
    let mut v___y_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6111_: u8 = 0;
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: u8 = 0;
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v___y_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6129_: u8 = 0;
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: usize = 0;
    let mut v___x_6135_: usize = 0;
    let mut v___x_6136_: u8 = 0;
    let mut v___x_6137_: usize = 0;
    let mut v___x_6138_: usize = 0;
    let mut v___x_6139_: u8 = 0;
    let mut v_binderName_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6143_: u8 = 0;
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: usize = 0;
    let mut v___x_6149_: usize = 0;
    let mut v___x_6150_: u8 = 0;
    let mut v___x_6151_: usize = 0;
    let mut v___x_6152_: usize = 0;
    let mut v___x_6153_: u8 = 0;
    let mut v_declName_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6158_: u8 = 0;
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: usize = 0;
    let mut v___x_6166_: usize = 0;
    let mut v___x_6167_: u8 = 0;
    let mut v___x_6168_: usize = 0;
    let mut v___x_6169_: usize = 0;
    let mut v___x_6170_: u8 = 0;
    let mut v_dummy_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: usize = 0;
    let mut v___x_6182_: usize = 0;
    let mut v___x_6183_: u8 = 0;
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: usize = 0;
    let mut v___x_6193_: usize = 0;
    let mut v___x_6194_: u8 = 0;
    let mut v___x_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_a_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6213_: u8 = 0;
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut v_a_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6221_: u8 = 0;
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6118_ = l_Lean_Core_checkSystem(v___x_6067_, v___y_6072_, v___y_6073_);
                if leanh::lean_obj_tag(v___x_6118_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6118_, 1);
                    leanh::lean_inc_ref(v_pre_6068_);
                    leanh::lean_inc(v___y_6073_);
                    leanh::lean_inc_ref(v___y_6072_);
                    leanh::lean_inc_ref(v_e_6069_);
                    v___x_6119_ = leanh::lean_apply_4(
                        v_pre_6068_,
                        v_e_6069_,
                        v___y_6072_,
                        v___y_6073_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6119_) == 0 {
                        v_a_6120_ = leanh::lean_ctor_get(v___x_6119_, 0);
                        v_isSharedCheck_6209_ =
                            (!leanh::lean_is_exclusive(v___x_6119_)) as u8;
                        if v_isSharedCheck_6209_ == 0 {
                            v___x_6122_ = v___x_6119_;
                            v_isShared_6123_ = v_isSharedCheck_6209_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6120_);
                            leanh::lean_dec(v___x_6119_);
                            v___x_6122_ = leanh::lean_box(0);
                            v_isShared_6123_ = v_isSharedCheck_6209_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_e_6069_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        v_a_6210_ = leanh::lean_ctor_get(v___x_6119_, 0);
                        v_isSharedCheck_6217_ =
                            (!leanh::lean_is_exclusive(v___x_6119_)) as u8;
                        if v_isSharedCheck_6217_ == 0 {
                            v___x_6212_ = v___x_6119_;
                            v_isShared_6213_ = v_isSharedCheck_6217_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6210_);
                            leanh::lean_dec(v___x_6119_);
                            v___x_6212_ = leanh::lean_box(0);
                            v_isShared_6213_ = v_isSharedCheck_6217_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_6070_);
                    leanh::lean_dec_ref(v_e_6069_);
                    leanh::lean_dec_ref(v_pre_6068_);
                    v_a_6218_ = leanh::lean_ctor_get(v___x_6118_, 0);
                    v_isSharedCheck_6225_ = (!leanh::lean_is_exclusive(v___x_6118_)) as u8;
                    if v_isSharedCheck_6225_ == 0 {
                        v___x_6220_ = v___x_6118_;
                        v_isShared_6221_ = v_isSharedCheck_6225_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6218_);
                        leanh::lean_dec(v___x_6118_);
                        v___x_6220_ = leanh::lean_box(0);
                        v_isShared_6221_ = v_isSharedCheck_6225_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6083_ == 0 {
                    leanh::lean_dec_ref(v___y_6079_);
                    leanh::lean_dec_ref(v___y_6076_);
                    v___x_6084_ = l_Lean_Expr_letE___override(
                        v___y_6077_,
                        v___y_6080_,
                        v___y_6082_,
                        v___y_6078_,
                        v___y_6081_,
                    );
                    v___x_6085_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6084_, v___y_6071_, v___y_6072_, v___y_6073_);
                    return v___x_6085_;
                } else {
                    v___x_6086_ = lean_ptr_addr(v___y_6076_);
                    leanh::lean_dec_ref(v___y_6076_);
                    v___x_6087_ = lean_ptr_addr(v___y_6078_);
                    v___x_6088_ = lean_usize_dec_eq(v___x_6086_, v___x_6087_);
                    if v___x_6088_ == 0 {
                        leanh::lean_dec_ref(v___y_6079_);
                        v___x_6089_ = l_Lean_Expr_letE___override(
                            v___y_6077_,
                            v___y_6080_,
                            v___y_6082_,
                            v___y_6078_,
                            v___y_6081_,
                        );
                        v___x_6090_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6089_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6090_;
                    } else {
                        leanh::lean_dec_ref(v___y_6082_);
                        leanh::lean_dec_ref(v___y_6080_);
                        leanh::lean_dec_ref(v___y_6078_);
                        leanh::lean_dec(v___y_6077_);
                        v___x_6091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6079_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6091_;
                    }
                }
            }
            2 => {
                if v___y_6098_ == 0 {
                    leanh::lean_dec_ref(v___y_6095_);
                    v___x_6099_ = l_Lean_Expr_lam___override(
                        v___y_6093_,
                        v___y_6094_,
                        v___y_6096_,
                        v___y_6097_,
                    );
                    v___x_6100_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6099_, v___y_6071_, v___y_6072_, v___y_6073_);
                    return v___x_6100_;
                } else {
                    v___x_6101_ = l_Lean_instBEqBinderInfo_beq(v___y_6097_, v___y_6097_);
                    if v___x_6101_ == 0 {
                        leanh::lean_dec_ref(v___y_6095_);
                        v___x_6102_ = l_Lean_Expr_lam___override(
                            v___y_6093_,
                            v___y_6094_,
                            v___y_6096_,
                            v___y_6097_,
                        );
                        v___x_6103_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6102_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6103_;
                    } else {
                        leanh::lean_dec_ref(v___y_6096_);
                        leanh::lean_dec_ref(v___y_6094_);
                        leanh::lean_dec(v___y_6093_);
                        v___x_6104_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6095_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6104_;
                    }
                }
            }
            3 => {
                if v___y_6111_ == 0 {
                    leanh::lean_dec_ref(v___y_6109_);
                    v___x_6112_ = l_Lean_Expr_forallE___override(
                        v___y_6106_,
                        v___y_6108_,
                        v___y_6110_,
                        v___y_6107_,
                    );
                    v___x_6113_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6112_, v___y_6071_, v___y_6072_, v___y_6073_);
                    return v___x_6113_;
                } else {
                    v___x_6114_ = l_Lean_instBEqBinderInfo_beq(v___y_6107_, v___y_6107_);
                    if v___x_6114_ == 0 {
                        leanh::lean_dec_ref(v___y_6109_);
                        v___x_6115_ = l_Lean_Expr_forallE___override(
                            v___y_6106_,
                            v___y_6108_,
                            v___y_6110_,
                            v___y_6107_,
                        );
                        v___x_6116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6115_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6116_;
                    } else {
                        leanh::lean_dec_ref(v___y_6110_);
                        leanh::lean_dec_ref(v___y_6108_);
                        leanh::lean_dec(v___y_6106_);
                        v___x_6117_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6109_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6117_;
                    }
                }
            }
            4 => match leanh::lean_obj_tag(v_a_6120_) {
                0 => {
                    leanh::lean_dec_ref(v_post_6070_);
                    leanh::lean_dec_ref(v_e_6069_);
                    leanh::lean_dec_ref(v_pre_6068_);
                    v_e_6199_ = leanh::lean_ctor_get(v_a_6120_, 0);
                    leanh::lean_inc_ref(v_e_6199_);
                    leanh::lean_dec_ref_known(v_a_6120_, 1);
                    if v_isShared_6123_ == 0 {
                        leanh::lean_ctor_set(v___x_6122_, 0, v_e_6199_);
                        v___x_6201_ = v___x_6122_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6202_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_e_6199_);
                        v___x_6201_ = v_reuseFailAlloc_6202_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_6122_);
                    leanh::lean_dec_ref(v_e_6069_);
                    v_e_6203_ = leanh::lean_ctor_get(v_a_6120_, 0);
                    leanh::lean_inc_ref(v_e_6203_);
                    leanh::lean_dec_ref_known(v_a_6120_, 1);
                    leanh::lean_inc_ref(v_post_6070_);
                    leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6204_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_e_6203_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if leanh::lean_obj_tag(v___x_6204_) == 0 {
                        v_a_6205_ = leanh::lean_ctor_get(v___x_6204_, 0);
                        leanh::lean_inc(v_a_6205_);
                        leanh::lean_dec_ref_known(v___x_6204_, 1);
                        v___x_6206_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v_a_6205_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6206_;
                    } else {
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6204_;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_6122_);
                    v_e_x3f_6207_ = leanh::lean_ctor_get(v_a_6120_, 0);
                    leanh::lean_inc(v_e_x3f_6207_);
                    leanh::lean_dec_ref_known(v_a_6120_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_6207_) == 0 {
                        v___y_6125_ = v_e_6069_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_6069_);
                        v_val_6208_ = leanh::lean_ctor_get(v_e_x3f_6207_, 0);
                        leanh::lean_inc(v_val_6208_);
                        leanh::lean_dec_ref_known(v_e_x3f_6207_, 1);
                        v___y_6125_ = v_val_6208_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match leanh::lean_obj_tag(v___y_6125_) {
                7 => {
                    v_binderName_6126_ = leanh::lean_ctor_get(v___y_6125_, 0);
                    leanh::lean_inc(v_binderName_6126_);
                    v_binderType_6127_ = leanh::lean_ctor_get(v___y_6125_, 1);
                    v_body_6128_ = leanh::lean_ctor_get(v___y_6125_, 2);
                    v_binderInfo_6129_ = leanh::lean_ctor_get_uint8(
                        v___y_6125_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6127_);
                    leanh::lean_inc_ref(v_post_6070_);
                    leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_binderType_6127_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if leanh::lean_obj_tag(v___x_6130_) == 0 {
                        v_a_6131_ = leanh::lean_ctor_get(v___x_6130_, 0);
                        leanh::lean_inc(v_a_6131_);
                        leanh::lean_dec_ref_known(v___x_6130_, 1);
                        leanh::lean_inc_ref(v_body_6128_);
                        leanh::lean_inc_ref(v_post_6070_);
                        leanh::lean_inc_ref(v_pre_6068_);
                        v___x_6132_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_body_6128_, v___y_6071_, v___y_6072_, v___y_6073_);
                        if leanh::lean_obj_tag(v___x_6132_) == 0 {
                            v_a_6133_ = leanh::lean_ctor_get(v___x_6132_, 0);
                            leanh::lean_inc(v_a_6133_);
                            leanh::lean_dec_ref_known(v___x_6132_, 1);
                            v___x_6134_ = lean_ptr_addr(v_binderType_6127_);
                            v___x_6135_ = lean_ptr_addr(v_a_6131_);
                            v___x_6136_ = lean_usize_dec_eq(v___x_6134_, v___x_6135_);
                            if v___x_6136_ == 0 {
                                v___y_6106_ = v_binderName_6126_;
                                v___y_6107_ = v_binderInfo_6129_;
                                v___y_6108_ = v_a_6131_;
                                v___y_6109_ = v___y_6125_;
                                v___y_6110_ = v_a_6133_;
                                v___y_6111_ = v___x_6136_;
                                state = 3;
                                continue;
                            } else {
                                v___x_6137_ = lean_ptr_addr(v_body_6128_);
                                v___x_6138_ = lean_ptr_addr(v_a_6133_);
                                v___x_6139_ = lean_usize_dec_eq(v___x_6137_, v___x_6138_);
                                v___y_6106_ = v_binderName_6126_;
                                v___y_6107_ = v_binderInfo_6129_;
                                v___y_6108_ = v_a_6131_;
                                v___y_6109_ = v___y_6125_;
                                v___y_6110_ = v_a_6133_;
                                v___y_6111_ = v___x_6139_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6131_);
                            leanh::lean_dec(v_binderName_6126_);
                            leanh::lean_dec_ref_known(v___y_6125_, 3);
                            leanh::lean_dec_ref(v_post_6070_);
                            leanh::lean_dec_ref(v_pre_6068_);
                            return v___x_6132_;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_6126_);
                        leanh::lean_dec_ref_known(v___y_6125_, 3);
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6130_;
                    }
                }
                6 => {
                    v_binderName_6140_ = leanh::lean_ctor_get(v___y_6125_, 0);
                    leanh::lean_inc(v_binderName_6140_);
                    v_binderType_6141_ = leanh::lean_ctor_get(v___y_6125_, 1);
                    v_body_6142_ = leanh::lean_ctor_get(v___y_6125_, 2);
                    v_binderInfo_6143_ = leanh::lean_ctor_get_uint8(
                        v___y_6125_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6141_);
                    leanh::lean_inc_ref(v_post_6070_);
                    leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6144_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_binderType_6141_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if leanh::lean_obj_tag(v___x_6144_) == 0 {
                        v_a_6145_ = leanh::lean_ctor_get(v___x_6144_, 0);
                        leanh::lean_inc(v_a_6145_);
                        leanh::lean_dec_ref_known(v___x_6144_, 1);
                        leanh::lean_inc_ref(v_body_6142_);
                        leanh::lean_inc_ref(v_post_6070_);
                        leanh::lean_inc_ref(v_pre_6068_);
                        v___x_6146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_body_6142_, v___y_6071_, v___y_6072_, v___y_6073_);
                        if leanh::lean_obj_tag(v___x_6146_) == 0 {
                            v_a_6147_ = leanh::lean_ctor_get(v___x_6146_, 0);
                            leanh::lean_inc(v_a_6147_);
                            leanh::lean_dec_ref_known(v___x_6146_, 1);
                            v___x_6148_ = lean_ptr_addr(v_binderType_6141_);
                            v___x_6149_ = lean_ptr_addr(v_a_6145_);
                            v___x_6150_ = lean_usize_dec_eq(v___x_6148_, v___x_6149_);
                            if v___x_6150_ == 0 {
                                v___y_6093_ = v_binderName_6140_;
                                v___y_6094_ = v_a_6145_;
                                v___y_6095_ = v___y_6125_;
                                v___y_6096_ = v_a_6147_;
                                v___y_6097_ = v_binderInfo_6143_;
                                v___y_6098_ = v___x_6150_;
                                state = 2;
                                continue;
                            } else {
                                v___x_6151_ = lean_ptr_addr(v_body_6142_);
                                v___x_6152_ = lean_ptr_addr(v_a_6147_);
                                v___x_6153_ = lean_usize_dec_eq(v___x_6151_, v___x_6152_);
                                v___y_6093_ = v_binderName_6140_;
                                v___y_6094_ = v_a_6145_;
                                v___y_6095_ = v___y_6125_;
                                v___y_6096_ = v_a_6147_;
                                v___y_6097_ = v_binderInfo_6143_;
                                v___y_6098_ = v___x_6153_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6145_);
                            leanh::lean_dec(v_binderName_6140_);
                            leanh::lean_dec_ref_known(v___y_6125_, 3);
                            leanh::lean_dec_ref(v_post_6070_);
                            leanh::lean_dec_ref(v_pre_6068_);
                            return v___x_6146_;
                        }
                    } else {
                        leanh::lean_dec(v_binderName_6140_);
                        leanh::lean_dec_ref_known(v___y_6125_, 3);
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6144_;
                    }
                }
                8 => {
                    v_declName_6154_ = leanh::lean_ctor_get(v___y_6125_, 0);
                    leanh::lean_inc(v_declName_6154_);
                    v_type_6155_ = leanh::lean_ctor_get(v___y_6125_, 1);
                    v_value_6156_ = leanh::lean_ctor_get(v___y_6125_, 2);
                    v_body_6157_ = leanh::lean_ctor_get(v___y_6125_, 3);
                    leanh::lean_inc_ref(v_body_6157_);
                    v_nondep_6158_ = leanh::lean_ctor_get_uint8(
                        v___y_6125_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_6155_);
                    leanh::lean_inc_ref(v_post_6070_);
                    leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_type_6155_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if leanh::lean_obj_tag(v___x_6159_) == 0 {
                        v_a_6160_ = leanh::lean_ctor_get(v___x_6159_, 0);
                        leanh::lean_inc(v_a_6160_);
                        leanh::lean_dec_ref_known(v___x_6159_, 1);
                        leanh::lean_inc_ref(v_value_6156_);
                        leanh::lean_inc_ref(v_post_6070_);
                        leanh::lean_inc_ref(v_pre_6068_);
                        v___x_6161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_value_6156_, v___y_6071_, v___y_6072_, v___y_6073_);
                        if leanh::lean_obj_tag(v___x_6161_) == 0 {
                            v_a_6162_ = leanh::lean_ctor_get(v___x_6161_, 0);
                            leanh::lean_inc(v_a_6162_);
                            leanh::lean_dec_ref_known(v___x_6161_, 1);
                            leanh::lean_inc_ref(v_body_6157_);
                            leanh::lean_inc_ref(v_post_6070_);
                            leanh::lean_inc_ref(v_pre_6068_);
                            v___x_6163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_body_6157_, v___y_6071_, v___y_6072_, v___y_6073_);
                            if leanh::lean_obj_tag(v___x_6163_) == 0 {
                                v_a_6164_ = leanh::lean_ctor_get(v___x_6163_, 0);
                                leanh::lean_inc(v_a_6164_);
                                leanh::lean_dec_ref_known(v___x_6163_, 1);
                                v___x_6165_ = lean_ptr_addr(v_type_6155_);
                                v___x_6166_ = lean_ptr_addr(v_a_6160_);
                                v___x_6167_ = lean_usize_dec_eq(v___x_6165_, v___x_6166_);
                                if v___x_6167_ == 0 {
                                    v___y_6076_ = v_body_6157_;
                                    v___y_6077_ = v_declName_6154_;
                                    v___y_6078_ = v_a_6164_;
                                    v___y_6079_ = v___y_6125_;
                                    v___y_6080_ = v_a_6160_;
                                    v___y_6081_ = v_nondep_6158_;
                                    v___y_6082_ = v_a_6162_;
                                    v___y_6083_ = v___x_6167_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_6168_ = lean_ptr_addr(v_value_6156_);
                                    v___x_6169_ = lean_ptr_addr(v_a_6162_);
                                    v___x_6170_ = lean_usize_dec_eq(v___x_6168_, v___x_6169_);
                                    v___y_6076_ = v_body_6157_;
                                    v___y_6077_ = v_declName_6154_;
                                    v___y_6078_ = v_a_6164_;
                                    v___y_6079_ = v___y_6125_;
                                    v___y_6080_ = v_a_6160_;
                                    v___y_6081_ = v_nondep_6158_;
                                    v___y_6082_ = v_a_6162_;
                                    v___y_6083_ = v___x_6170_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_6162_);
                                leanh::lean_dec(v_a_6160_);
                                leanh::lean_dec_ref(v_body_6157_);
                                leanh::lean_dec(v_declName_6154_);
                                leanh::lean_dec_ref_known(v___y_6125_, 4);
                                leanh::lean_dec_ref(v_post_6070_);
                                leanh::lean_dec_ref(v_pre_6068_);
                                return v___x_6163_;
                            }
                        } else {
                            leanh::lean_dec(v_a_6160_);
                            leanh::lean_dec_ref(v_body_6157_);
                            leanh::lean_dec_ref_known(v___y_6125_, 4);
                            leanh::lean_dec(v_declName_6154_);
                            leanh::lean_dec_ref(v_post_6070_);
                            leanh::lean_dec_ref(v_pre_6068_);
                            return v___x_6161_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_6157_);
                        leanh::lean_dec_ref_known(v___y_6125_, 4);
                        leanh::lean_dec(v_declName_6154_);
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6159_;
                    }
                }
                5 => {
                    v_dummy_6171_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_6172_ = l_Lean_Expr_getAppNumArgs(v___y_6125_);
                    leanh::lean_inc(v_nargs_6172_);
                    v___x_6173_ = lean_mk_array(v_nargs_6172_, v_dummy_6171_);
                    v___x_6174_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6175_ = lean_nat_sub(v_nargs_6172_, v___x_6174_);
                    leanh::lean_dec(v_nargs_6172_);
                    v___x_6176_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_6068_, v_post_6070_, v___y_6125_, v___x_6173_, v___x_6175_, v___y_6071_, v___y_6072_, v___y_6073_);
                    return v___x_6176_;
                }
                10 => {
                    v_data_6177_ = leanh::lean_ctor_get(v___y_6125_, 0);
                    v_expr_6178_ = leanh::lean_ctor_get(v___y_6125_, 1);
                    leanh::lean_inc_ref(v_expr_6178_);
                    leanh::lean_inc_ref(v_post_6070_);
                    leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_expr_6178_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if leanh::lean_obj_tag(v___x_6179_) == 0 {
                        v_a_6180_ = leanh::lean_ctor_get(v___x_6179_, 0);
                        leanh::lean_inc(v_a_6180_);
                        leanh::lean_dec_ref_known(v___x_6179_, 1);
                        v___x_6181_ = lean_ptr_addr(v_expr_6178_);
                        v___x_6182_ = lean_ptr_addr(v_a_6180_);
                        v___x_6183_ = lean_usize_dec_eq(v___x_6181_, v___x_6182_);
                        if v___x_6183_ == 0 {
                            leanh::lean_inc(v_data_6177_);
                            leanh::lean_dec_ref_known(v___y_6125_, 2);
                            v___x_6184_ = l_Lean_Expr_mdata___override(v_data_6177_, v_a_6180_);
                            v___x_6185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6184_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6185_;
                        } else {
                            leanh::lean_dec(v_a_6180_);
                            v___x_6186_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6125_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6186_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6125_, 2);
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6179_;
                    }
                }
                11 => {
                    v_typeName_6187_ = leanh::lean_ctor_get(v___y_6125_, 0);
                    v_idx_6188_ = leanh::lean_ctor_get(v___y_6125_, 1);
                    v_struct_6189_ = leanh::lean_ctor_get(v___y_6125_, 2);
                    leanh::lean_inc_ref(v_struct_6189_);
                    leanh::lean_inc_ref(v_post_6070_);
                    leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_struct_6189_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if leanh::lean_obj_tag(v___x_6190_) == 0 {
                        v_a_6191_ = leanh::lean_ctor_get(v___x_6190_, 0);
                        leanh::lean_inc(v_a_6191_);
                        leanh::lean_dec_ref_known(v___x_6190_, 1);
                        v___x_6192_ = lean_ptr_addr(v_struct_6189_);
                        v___x_6193_ = lean_ptr_addr(v_a_6191_);
                        v___x_6194_ = lean_usize_dec_eq(v___x_6192_, v___x_6193_);
                        if v___x_6194_ == 0 {
                            leanh::lean_inc(v_idx_6188_);
                            leanh::lean_inc(v_typeName_6187_);
                            leanh::lean_dec_ref_known(v___y_6125_, 3);
                            v___x_6195_ = l_Lean_Expr_proj___override(
                                v_typeName_6187_,
                                v_idx_6188_,
                                v_a_6191_,
                            );
                            v___x_6196_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6195_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6196_;
                        } else {
                            leanh::lean_dec(v_a_6191_);
                            v___x_6197_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6125_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6197_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6125_, 3);
                        leanh::lean_dec_ref(v_post_6070_);
                        leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6190_;
                    }
                }
                _ => {
                    v___x_6198_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6125_, v___y_6071_, v___y_6072_, v___y_6073_);
                    return v___x_6198_;
                }
            },
            6 => {
                return v___x_6201_;
            }
            7 => {
                if v_isShared_6213_ == 0 {
                    v___x_6215_ = v___x_6212_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6216_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
                    v___x_6215_ = v_reuseFailAlloc_6216_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6215_;
            }
            9 => {
                if v_isShared_6221_ == 0 {
                    v___x_6223_ = v___x_6220_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6224_, 0, v_a_6218_);
                    v___x_6223_ = v_reuseFailAlloc_6224_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(
    mut v___x_6226_: *mut leanh::LeanObject,
    mut v_pre_6227_: *mut leanh::LeanObject,
    mut v_e_6228_: *mut leanh::LeanObject,
    mut v_post_6229_: *mut leanh::LeanObject,
    mut v___y_6230_: *mut leanh::LeanObject,
    mut v___y_6231_: *mut leanh::LeanObject,
    mut v___y_6232_: *mut leanh::LeanObject,
    mut v___y_6233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_6226_, v_pre_6227_, v_e_6228_, v_post_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
    leanh::lean_dec(v___y_6232_);
    leanh::lean_dec_ref(v___y_6231_);
    leanh::lean_dec(v___y_6230_);
    return v_res_6234_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(
    mut v_pre_6235_: *mut leanh::LeanObject,
    mut v_post_6236_: *mut leanh::LeanObject,
    mut v_e_6237_: *mut leanh::LeanObject,
    mut v_a_6238_: *mut leanh::LeanObject,
    mut v___y_6239_: *mut leanh::LeanObject,
    mut v___y_6240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v___x_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6261_: u8 = 0;
    let mut v_unused_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6266_: u8 = 0;
    let mut v___x_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v_val_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6275_: u8 = 0;
    let mut v_a_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6279_: u8 = 0;
    let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_6238_);
                v___x_6242_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_6242_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6242_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6242_, 2, v_a_6238_);
                v___x_6243_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(leanh::lean_box(0), v___x_6242_, v___y_6239_, v___y_6240_);
                if leanh::lean_obj_tag(v___x_6243_) == 0 {
                    v_a_6244_ = leanh::lean_ctor_get(v___x_6243_, 0);
                    v_isSharedCheck_6275_ = (!leanh::lean_is_exclusive(v___x_6243_)) as u8;
                    if v_isSharedCheck_6275_ == 0 {
                        v___x_6246_ = v___x_6243_;
                        v_isShared_6247_ = v_isSharedCheck_6275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6244_);
                        leanh::lean_dec(v___x_6243_);
                        v___x_6246_ = leanh::lean_box(0);
                        v_isShared_6247_ = v_isSharedCheck_6275_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6237_);
                    leanh::lean_dec_ref(v_post_6236_);
                    leanh::lean_dec_ref(v_pre_6235_);
                    v_a_6276_ = leanh::lean_ctor_get(v___x_6243_, 0);
                    v_isSharedCheck_6283_ = (!leanh::lean_is_exclusive(v___x_6243_)) as u8;
                    if v_isSharedCheck_6283_ == 0 {
                        v___x_6278_ = v___x_6243_;
                        v_isShared_6279_ = v_isSharedCheck_6283_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6276_);
                        leanh::lean_dec(v___x_6243_);
                        v___x_6278_ = leanh::lean_box(0);
                        v_isShared_6279_ = v_isSharedCheck_6283_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_6244_, v_e_6237_);
                leanh::lean_dec(v_a_6244_);
                if leanh::lean_obj_tag(v___x_6248_) == 0 {
                    leanh::lean_del_object(v___x_6246_);
                    v___x_6249_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0;
                    leanh::lean_inc_ref(v_e_6237_);
                    v___f_6250_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    leanh::lean_closure_set(v___f_6250_, 0, v___x_6249_);
                    leanh::lean_closure_set(v___f_6250_, 1, v_pre_6235_);
                    leanh::lean_closure_set(v___f_6250_, 2, v_e_6237_);
                    leanh::lean_closure_set(v___f_6250_, 3, v_post_6236_);
                    v___x_6251_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_6250_, v_a_6238_, v___y_6239_, v___y_6240_);
                    if leanh::lean_obj_tag(v___x_6251_) == 0 {
                        v_a_6252_ = leanh::lean_ctor_get(v___x_6251_, 0);
                        leanh::lean_inc_n(v_a_6252_, 2);
                        leanh::lean_dec_ref_known(v___x_6251_, 1);
                        leanh::lean_inc(v_a_6238_);
                        v___f_6253_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_6253_, 0, v_a_6238_);
                        leanh::lean_closure_set(v___f_6253_, 1, v_e_6237_);
                        leanh::lean_closure_set(v___f_6253_, 2, v_a_6252_);
                        v___x_6254_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(leanh::lean_box(0), v___f_6253_, v___y_6239_, v___y_6240_);
                        if leanh::lean_obj_tag(v___x_6254_) == 0 {
                            v_isSharedCheck_6261_ =
                                (!leanh::lean_is_exclusive(v___x_6254_)) as u8;
                            if v_isSharedCheck_6261_ == 0 {
                                v_unused_6262_ = leanh::lean_ctor_get(v___x_6254_, 0);
                                leanh::lean_dec(v_unused_6262_);
                                v___x_6256_ = v___x_6254_;
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_6254_);
                                v___x_6256_ = leanh::lean_box(0);
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6252_);
                            v_a_6263_ = leanh::lean_ctor_get(v___x_6254_, 0);
                            v_isSharedCheck_6270_ =
                                (!leanh::lean_is_exclusive(v___x_6254_)) as u8;
                            if v_isSharedCheck_6270_ == 0 {
                                v___x_6265_ = v___x_6254_;
                                v_isShared_6266_ = v_isSharedCheck_6270_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6263_);
                                leanh::lean_dec(v___x_6254_);
                                v___x_6265_ = leanh::lean_box(0);
                                v_isShared_6266_ = v_isSharedCheck_6270_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6237_);
                        return v___x_6251_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6237_);
                    leanh::lean_dec_ref(v_post_6236_);
                    leanh::lean_dec_ref(v_pre_6235_);
                    v_val_6271_ = leanh::lean_ctor_get(v___x_6248_, 0);
                    leanh::lean_inc(v_val_6271_);
                    leanh::lean_dec_ref_known(v___x_6248_, 1);
                    if v_isShared_6247_ == 0 {
                        leanh::lean_ctor_set(v___x_6246_, 0, v_val_6271_);
                        v___x_6273_ = v___x_6246_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_val_6271_);
                        v___x_6273_ = v_reuseFailAlloc_6274_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6257_ == 0 {
                    leanh::lean_ctor_set(v___x_6256_, 0, v_a_6252_);
                    v___x_6259_ = v___x_6256_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6252_);
                    v___x_6259_ = v_reuseFailAlloc_6260_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6259_;
            }
            4 => {
                if v_isShared_6266_ == 0 {
                    v___x_6268_ = v___x_6265_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_a_6263_);
                    v___x_6268_ = v_reuseFailAlloc_6269_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6268_;
            }
            6 => {
                return v___x_6273_;
            }
            7 => {
                if v_isShared_6279_ == 0 {
                    v___x_6281_ = v___x_6278_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6282_, 0, v_a_6276_);
                    v___x_6281_ = v_reuseFailAlloc_6282_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(
    mut v_pre_6284_: *mut leanh::LeanObject,
    mut v_post_6285_: *mut leanh::LeanObject,
    mut v_e_6286_: *mut leanh::LeanObject,
    mut v_a_6287_: *mut leanh::LeanObject,
    mut v___y_6288_: *mut leanh::LeanObject,
    mut v___y_6289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v_e_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_a_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v___x_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_6285_);
                leanh::lean_inc(v___y_6289_);
                leanh::lean_inc_ref(v___y_6288_);
                leanh::lean_inc_ref(v_e_6286_);
                v___x_6291_ = leanh::lean_apply_4(
                    v_post_6285_,
                    v_e_6286_,
                    v___y_6288_,
                    v___y_6289_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6291_) == 0 {
                    v_a_6292_ = leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6310_ = (!leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v___x_6294_ = v___x_6291_;
                        v_isShared_6295_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6292_);
                        leanh::lean_dec(v___x_6291_);
                        v___x_6294_ = leanh::lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6286_);
                    leanh::lean_dec_ref(v_post_6285_);
                    leanh::lean_dec_ref(v_pre_6284_);
                    v_a_6311_ = leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6318_ = (!leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6318_ == 0 {
                        v___x_6313_ = v___x_6291_;
                        v_isShared_6314_ = v_isSharedCheck_6318_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6311_);
                        leanh::lean_dec(v___x_6291_);
                        v___x_6313_ = leanh::lean_box(0);
                        v_isShared_6314_ = v_isSharedCheck_6318_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_6292_) {
                0 => {
                    leanh::lean_dec_ref(v_e_6286_);
                    leanh::lean_dec_ref(v_post_6285_);
                    leanh::lean_dec_ref(v_pre_6284_);
                    v_e_6296_ = leanh::lean_ctor_get(v_a_6292_, 0);
                    leanh::lean_inc_ref(v_e_6296_);
                    leanh::lean_dec_ref_known(v_a_6292_, 1);
                    if v_isShared_6295_ == 0 {
                        leanh::lean_ctor_set(v___x_6294_, 0, v_e_6296_);
                        v___x_6298_ = v___x_6294_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_e_6296_);
                        v___x_6298_ = v_reuseFailAlloc_6299_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_6294_);
                    leanh::lean_dec_ref(v_e_6286_);
                    v_e_6300_ = leanh::lean_ctor_get(v_a_6292_, 0);
                    leanh::lean_inc_ref(v_e_6300_);
                    leanh::lean_dec_ref_known(v_a_6292_, 1);
                    v___x_6301_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6284_, v_post_6285_, v_e_6300_, v_a_6287_, v___y_6288_, v___y_6289_);
                    return v___x_6301_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_6285_);
                    leanh::lean_dec_ref(v_pre_6284_);
                    v_e_x3f_6302_ = leanh::lean_ctor_get(v_a_6292_, 0);
                    leanh::lean_inc(v_e_x3f_6302_);
                    leanh::lean_dec_ref_known(v_a_6292_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_6302_) == 0 {
                        if v_isShared_6295_ == 0 {
                            leanh::lean_ctor_set(v___x_6294_, 0, v_e_6286_);
                            v___x_6304_ = v___x_6294_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6305_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_e_6286_);
                            v___x_6304_ = v_reuseFailAlloc_6305_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6286_);
                        v_val_6306_ = leanh::lean_ctor_get(v_e_x3f_6302_, 0);
                        leanh::lean_inc(v_val_6306_);
                        leanh::lean_dec_ref_known(v_e_x3f_6302_, 1);
                        if v_isShared_6295_ == 0 {
                            leanh::lean_ctor_set(v___x_6294_, 0, v_val_6306_);
                            v___x_6308_ = v___x_6294_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6309_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_val_6306_);
                            v___x_6308_ = v_reuseFailAlloc_6309_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_6298_;
            }
            3 => {
                return v___x_6304_;
            }
            4 => {
                return v___x_6308_;
            }
            5 => {
                if v_isShared_6314_ == 0 {
                    v___x_6316_ = v___x_6313_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_a_6311_);
                    v___x_6316_ = v_reuseFailAlloc_6317_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(
    mut v_pre_6319_: *mut leanh::LeanObject,
    mut v_post_6320_: *mut leanh::LeanObject,
    mut v_e_6321_: *mut leanh::LeanObject,
    mut v_a_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6326_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6319_, v_post_6320_, v_e_6321_, v_a_6322_, v___y_6323_, v___y_6324_);
    leanh::lean_dec(v___y_6324_);
    leanh::lean_dec_ref(v___y_6323_);
    leanh::lean_dec(v_a_6322_);
    return v_res_6326_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(
    mut v_pre_6327_: *mut leanh::LeanObject,
    mut v_post_6328_: *mut leanh::LeanObject,
    mut v_sz_6329_: *mut leanh::LeanObject,
    mut v_i_6330_: *mut leanh::LeanObject,
    mut v_bs_6331_: *mut leanh::LeanObject,
    mut v___y_6332_: *mut leanh::LeanObject,
    mut v___y_6333_: *mut leanh::LeanObject,
    mut v___y_6334_: *mut leanh::LeanObject,
    mut v___y_6335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6336_: usize = 0;
    let mut v_i_boxed_6337_: usize = 0;
    let mut v_res_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6336_ = leanh::lean_unbox_usize(v_sz_6329_);
    leanh::lean_dec(v_sz_6329_);
    v_i_boxed_6337_ = leanh::lean_unbox_usize(v_i_6330_);
    leanh::lean_dec(v_i_6330_);
    v_res_6338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_6327_, v_post_6328_, v_sz_boxed_6336_, v_i_boxed_6337_, v_bs_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    leanh::lean_dec(v___y_6334_);
    leanh::lean_dec_ref(v___y_6333_);
    leanh::lean_dec(v___y_6332_);
    return v_res_6338_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(
    mut v_pre_6339_: *mut leanh::LeanObject,
    mut v_post_6340_: *mut leanh::LeanObject,
    mut v_x_6341_: *mut leanh::LeanObject,
    mut v_x_6342_: *mut leanh::LeanObject,
    mut v_x_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
    mut v___y_6346_: *mut leanh::LeanObject,
    mut v___y_6347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6348_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_6339_, v_post_6340_, v_x_6341_, v_x_6342_, v_x_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
    leanh::lean_dec(v___y_6346_);
    leanh::lean_dec_ref(v___y_6345_);
    leanh::lean_dec(v___y_6344_);
    return v_res_6348_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(
    mut v_pre_6349_: *mut leanh::LeanObject,
    mut v_post_6350_: *mut leanh::LeanObject,
    mut v_e_6351_: *mut leanh::LeanObject,
    mut v_a_6352_: *mut leanh::LeanObject,
    mut v___y_6353_: *mut leanh::LeanObject,
    mut v___y_6354_: *mut leanh::LeanObject,
    mut v___y_6355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6356_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6349_, v_post_6350_, v_e_6351_, v_a_6352_, v___y_6353_, v___y_6354_);
    leanh::lean_dec(v___y_6354_);
    leanh::lean_dec_ref(v___y_6353_);
    leanh::lean_dec(v_a_6352_);
    return v_res_6356_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6357_ = leanh::lean_box(0);
    v___x_6358_ = leanh::lean_unsigned_to_nat(16);
    v___x_6359_ = lean_mk_array(v___x_6358_, v___x_6357_);
    return v___x_6359_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
    v___x_6361_ = leanh::lean_unsigned_to_nat(0);
    v___x_6362_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6362_, 0, v___x_6361_);
    leanh::lean_ctor_set(v___x_6362_, 1, v___x_6360_);
    return v___x_6362_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6363_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
    v___x_6364_ =
        leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_6364_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6364_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_6364_, 2, v___x_6363_);
    return v___x_6364_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(
    mut v_input_6365_: *mut leanh::LeanObject,
    mut v_pre_6366_: *mut leanh::LeanObject,
    mut v_post_6367_: *mut leanh::LeanObject,
    mut v___y_6368_: *mut leanh::LeanObject,
    mut v___y_6369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6380_: u8 = 0;
    let mut v___x_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6384_: u8 = 0;
    let mut v_unused_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6371_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
                v___x_6372_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(leanh::lean_box(0), v___x_6371_, v___y_6368_, v___y_6369_);
                v_a_6373_ = leanh::lean_ctor_get(v___x_6372_, 0);
                leanh::lean_inc(v_a_6373_);
                leanh::lean_dec_ref(v___x_6372_);
                v___x_6374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6366_, v_post_6367_, v_input_6365_, v_a_6373_, v___y_6368_, v___y_6369_);
                if leanh::lean_obj_tag(v___x_6374_) == 0 {
                    v_a_6375_ = leanh::lean_ctor_get(v___x_6374_, 0);
                    leanh::lean_inc(v_a_6375_);
                    leanh::lean_dec_ref_known(v___x_6374_, 1);
                    v___x_6376_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_6376_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_6376_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_6376_, 2, v_a_6373_);
                    v___x_6377_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(leanh::lean_box(0), v___x_6376_, v___y_6368_, v___y_6369_);
                    v_isSharedCheck_6384_ = (!leanh::lean_is_exclusive(v___x_6377_)) as u8;
                    if v_isSharedCheck_6384_ == 0 {
                        v_unused_6385_ = leanh::lean_ctor_get(v___x_6377_, 0);
                        leanh::lean_dec(v_unused_6385_);
                        v___x_6379_ = v___x_6377_;
                        v_isShared_6380_ = v_isSharedCheck_6384_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6377_);
                        v___x_6379_ = leanh::lean_box(0);
                        v_isShared_6380_ = v_isSharedCheck_6384_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6373_);
                    return v___x_6374_;
                }
            }
            1 => {
                if v_isShared_6380_ == 0 {
                    leanh::lean_ctor_set(v___x_6379_, 0, v_a_6375_);
                    v___x_6382_ = v___x_6379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6383_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_a_6375_);
                    v___x_6382_ = v_reuseFailAlloc_6383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(
    mut v_input_6386_: *mut leanh::LeanObject,
    mut v_pre_6387_: *mut leanh::LeanObject,
    mut v_post_6388_: *mut leanh::LeanObject,
    mut v___y_6389_: *mut leanh::LeanObject,
    mut v___y_6390_: *mut leanh::LeanObject,
    mut v___y_6391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6392_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(
        v_input_6386_,
        v_pre_6387_,
        v_post_6388_,
        v___y_6389_,
        v___y_6390_,
    );
    leanh::lean_dec(v___y_6390_);
    leanh::lean_dec_ref(v___y_6389_);
    return v_res_6392_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData(
    mut v_e_6396_: *mut leanh::LeanObject,
    mut v_a_6397_: *mut leanh::LeanObject,
    mut v_a_6398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6400_ = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0;
    v___x_6401_ = lean_find_expr(v___f_6400_, v_e_6396_);
    if leanh::lean_obj_tag(v___x_6401_) == 0 {
        let mut v___x_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6402_, 0, v_e_6396_);
        return v___x_6402_;
    } else {
        let mut v_pre_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_6401_, 1);
        v_pre_6403_ = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1;
        v___f_6404_ = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2;
        v___x_6405_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(
            v_e_6396_,
            v_pre_6403_,
            v___f_6404_,
            v_a_6397_,
            v_a_6398_,
        );
        return v___x_6405_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(
    mut v_e_6406_: *mut leanh::LeanObject,
    mut v_a_6407_: *mut leanh::LeanObject,
    mut v_a_6408_: *mut leanh::LeanObject,
    mut v_a_6409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6410_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_6406_, v_a_6407_, v_a_6408_);
    leanh::lean_dec(v_a_6408_);
    leanh::lean_dec_ref(v_a_6407_);
    return v_res_6410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(
    mut v_00_u03b2_6411_: *mut leanh::LeanObject,
    mut v_m_6412_: *mut leanh::LeanObject,
    mut v_a_6413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_6412_, v_a_6413_);
    return v___x_6414_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_6415_: *mut leanh::LeanObject,
    mut v_m_6416_: *mut leanh::LeanObject,
    mut v_a_6417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_6415_, v_m_6416_, v_a_6417_);
    leanh::lean_dec_ref(v_a_6417_);
    leanh::lean_dec_ref(v_m_6416_);
    return v_res_6418_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_6419_: *mut leanh::LeanObject,
    mut v_ref_6420_: *mut leanh::LeanObject,
    mut v___y_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6424_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_6420_);
    return v___x_6424_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_6425_: *mut leanh::LeanObject,
    mut v_ref_6426_: *mut leanh::LeanObject,
    mut v___y_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
    mut v___y_6429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_6425_, v_ref_6426_, v___y_6427_, v___y_6428_);
    leanh::lean_dec(v___y_6428_);
    leanh::lean_dec_ref(v___y_6427_);
    return v_res_6430_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_6431_: *mut leanh::LeanObject,
    mut v___y_6432_: *mut leanh::LeanObject,
    mut v___y_6433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6435_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_6435_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_6436_: *mut leanh::LeanObject,
    mut v___y_6437_: *mut leanh::LeanObject,
    mut v___y_6438_: *mut leanh::LeanObject,
    mut v___y_6439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6440_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_6436_, v___y_6437_, v___y_6438_);
    leanh::lean_dec(v___y_6438_);
    leanh::lean_dec_ref(v___y_6437_);
    return v_res_6440_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(
    mut v_00_u03b1_6441_: *mut leanh::LeanObject,
    mut v_x_6442_: *mut leanh::LeanObject,
    mut v___y_6443_: *mut leanh::LeanObject,
    mut v___y_6444_: *mut leanh::LeanObject,
    mut v___y_6445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6447_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
    return v___x_6447_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_6448_: *mut leanh::LeanObject,
    mut v_x_6449_: *mut leanh::LeanObject,
    mut v___y_6450_: *mut leanh::LeanObject,
    mut v___y_6451_: *mut leanh::LeanObject,
    mut v___y_6452_: *mut leanh::LeanObject,
    mut v___y_6453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6454_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_6448_, v_x_6449_, v___y_6450_, v___y_6451_, v___y_6452_);
    leanh::lean_dec(v___y_6452_);
    leanh::lean_dec_ref(v___y_6451_);
    leanh::lean_dec(v___y_6450_);
    return v_res_6454_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(
    mut v_00_u03b2_6455_: *mut leanh::LeanObject,
    mut v_m_6456_: *mut leanh::LeanObject,
    mut v_a_6457_: *mut leanh::LeanObject,
    mut v_b_6458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_6456_, v_a_6457_, v_b_6458_);
    return v___x_6459_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_6460_: *mut leanh::LeanObject,
    mut v_a_6461_: *mut leanh::LeanObject,
    mut v_x_6462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_6461_, v_x_6462_);
    return v___x_6463_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_6464_: *mut leanh::LeanObject,
    mut v_a_6465_: *mut leanh::LeanObject,
    mut v_x_6466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6467_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_6464_, v_a_6465_, v_x_6466_);
    leanh::lean_dec(v_x_6466_);
    leanh::lean_dec_ref(v_a_6465_);
    return v_res_6467_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_6468_: *mut leanh::LeanObject,
    mut v_a_6469_: *mut leanh::LeanObject,
    mut v_x_6470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6471_: u8 = 0;
    v___x_6471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_6469_, v_x_6470_);
    return v___x_6471_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_6472_: *mut leanh::LeanObject,
    mut v_a_6473_: *mut leanh::LeanObject,
    mut v_x_6474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6475_: u8 = 0;
    let mut v_r_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_6472_, v_a_6473_, v_x_6474_);
    leanh::lean_dec(v_x_6474_);
    leanh::lean_dec_ref(v_a_6473_);
    v_r_6476_ = leanh::lean_box((v_res_6475_) as usize);
    return v_r_6476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_6477_: *mut leanh::LeanObject,
    mut v_data_6478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_data_6478_);
    return v___x_6479_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_6480_: *mut leanh::LeanObject,
    mut v_a_6481_: *mut leanh::LeanObject,
    mut v_b_6482_: *mut leanh::LeanObject,
    mut v_x_6483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_6481_, v_b_6482_, v_x_6483_);
    return v___x_6484_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_6485_: *mut leanh::LeanObject,
    mut v_i_6486_: *mut leanh::LeanObject,
    mut v_source_6487_: *mut leanh::LeanObject,
    mut v_target_6488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_6486_, v_source_6487_, v_target_6488_);
    return v___x_6489_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_6490_: *mut leanh::LeanObject,
    mut v_x_6491_: *mut leanh::LeanObject,
    mut v_x_6492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_6491_, v_x_6492_);
    return v___x_6493_;
}
pub unsafe fn l_Lean_Meta_Grind_foldProjs(
    mut v_e_6494_: *mut leanh::LeanObject,
    mut v_a_6495_: *mut leanh::LeanObject,
    mut v_a_6496_: *mut leanh::LeanObject,
    mut v_a_6497_: *mut leanh::LeanObject,
    mut v_a_6498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6500_ = l_Lean_Meta_Sym_foldProjs(v_e_6494_, v_a_6495_, v_a_6496_, v_a_6497_, v_a_6498_);
    return v___x_6500_;
}
pub unsafe fn l_Lean_Meta_Grind_foldProjs___boxed(
    mut v_e_6501_: *mut leanh::LeanObject,
    mut v_a_6502_: *mut leanh::LeanObject,
    mut v_a_6503_: *mut leanh::LeanObject,
    mut v_a_6504_: *mut leanh::LeanObject,
    mut v_a_6505_: *mut leanh::LeanObject,
    mut v_a_6506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6507_ =
        l_Lean_Meta_Grind_foldProjs(v_e_6501_, v_a_6502_, v_a_6503_, v_a_6504_, v_a_6505_);
    leanh::lean_dec(v_a_6505_);
    leanh::lean_dec_ref(v_a_6504_);
    leanh::lean_dec(v_a_6503_);
    leanh::lean_dec_ref(v_a_6502_);
    return v_res_6507_;
}
pub unsafe fn l_Lean_Meta_Grind_normalize___boxed(
    mut v_e_6515_: *mut leanh::LeanObject,
    mut v_config_6516_: *mut leanh::LeanObject,
    mut v_a_6517_: *mut leanh::LeanObject,
    mut v_a_6518_: *mut leanh::LeanObject,
    mut v_a_6519_: *mut leanh::LeanObject,
    mut v_a_6520_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_6521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6522_ = lean_grind_normalize(
        v_e_6515_,
        v_config_6516_,
        v_a_6517_,
        v_a_6518_,
        v_a_6519_,
        v_a_6520_,
    );
    return v_res_6522_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6530_ = leanh::lean_box(0);
    v___x_6531_ = l_Lean_Meta_Grind_markAsMatchCond___closed__3;
    v___x_6532_ = l_Lean_mkConst(v___x_6531_, v___x_6530_);
    return v___x_6532_;
}
pub unsafe fn l_Lean_Meta_Grind_markAsMatchCond(
    mut v_e_6533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6534_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsMatchCond___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsMatchCond___closed__4_once),
        _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4,
    );
    v___x_6535_ = l_Lean_Expr_app___override(v___x_6534_, v_e_6533_);
    return v___x_6535_;
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCond(mut v_e_6536_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: u8 = 0;
    v___x_6537_ = l_Lean_Meta_Grind_markAsMatchCond___closed__3;
    v___x_6538_ = leanh::lean_unsigned_to_nat(1);
    v___x_6539_ = l_Lean_Expr_isAppOfArity(v_e_6536_, v___x_6537_, v___x_6538_);
    return v___x_6539_;
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCond___boxed(
    mut v_e_6540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6541_: u8 = 0;
    let mut v_r_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6541_ = l_Lean_Meta_Grind_isMatchCond(v_e_6540_);
    leanh::lean_dec_ref(v_e_6540_);
    v_r_6542_ = leanh::lean_box((v_res_6541_) as usize);
    return v_r_6542_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6548_ = leanh::lean_box(0);
    v___x_6549_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
    v___x_6550_ = l_Lean_mkConst(v___x_6549_, v___x_6548_);
    return v___x_6550_;
}
pub unsafe fn l_Lean_Meta_Grind_markAsPreMatchCond(
    mut v_e_6551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6552_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once),
        _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2,
    );
    v___x_6553_ = l_Lean_Expr_app___override(v___x_6552_, v_e_6551_);
    return v___x_6553_;
}
pub unsafe fn l_Lean_Meta_Grind_isPreMatchCond(mut v_e_6554_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: u8 = 0;
    v___x_6555_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
    v___x_6556_ = leanh::lean_unsigned_to_nat(1);
    v___x_6557_ = l_Lean_Expr_isAppOfArity(v_e_6554_, v___x_6555_, v___x_6556_);
    return v___x_6557_;
}
pub unsafe fn l_Lean_Meta_Grind_isPreMatchCond___boxed(
    mut v_e_6558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6559_: u8 = 0;
    let mut v_r_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6559_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_6558_);
    leanh::lean_dec_ref(v_e_6558_);
    v_r_6560_ = leanh::lean_box((v_res_6559_) as usize);
    return v_r_6560_;
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond___redArg(
    mut v_e_6563_: *mut leanh::LeanObject,
    mut v_a_6564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6570_: u8 = 0;
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: u8 = 0;
    let mut v___x_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6583_: u8 = 0;
    let mut v_a_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_6563_);
                v___x_6566_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6563_, v_a_6564_);
                if leanh::lean_obj_tag(v___x_6566_) == 0 {
                    v_a_6567_ = leanh::lean_ctor_get(v___x_6566_, 0);
                    v_isSharedCheck_6583_ = (!leanh::lean_is_exclusive(v___x_6566_)) as u8;
                    if v_isSharedCheck_6583_ == 0 {
                        v___x_6569_ = v___x_6566_;
                        v_isShared_6570_ = v_isSharedCheck_6583_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6567_);
                        leanh::lean_dec(v___x_6566_);
                        v___x_6569_ = leanh::lean_box(0);
                        v_isShared_6570_ = v_isSharedCheck_6583_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6563_);
                    v_a_6584_ = leanh::lean_ctor_get(v___x_6566_, 0);
                    v_isSharedCheck_6591_ = (!leanh::lean_is_exclusive(v___x_6566_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6566_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6584_);
                        leanh::lean_dec(v___x_6566_);
                        v___x_6586_ = leanh::lean_box(0);
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6576_ = l_Lean_Expr_cleanupAnnotations(v_a_6567_);
                v___x_6577_ = l_Lean_Expr_isApp(v___x_6576_);
                if v___x_6577_ == 0 {
                    leanh::lean_dec_ref(v___x_6576_);
                    leanh::lean_dec_ref(v_e_6563_);
                    state = 2;
                    continue;
                } else {
                    v___x_6578_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6576_);
                    v___x_6579_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
                    v___x_6580_ = l_Lean_Expr_isConstOf(v___x_6578_, v___x_6579_);
                    leanh::lean_dec_ref(v___x_6578_);
                    if v___x_6580_ == 0 {
                        leanh::lean_dec_ref(v_e_6563_);
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_6569_);
                        v___x_6581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6581_, 0, v_e_6563_);
                        v___x_6582_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6582_, 0, v___x_6581_);
                        return v___x_6582_;
                    }
                }
            }
            2 => {
                v___x_6572_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0;
                if v_isShared_6570_ == 0 {
                    leanh::lean_ctor_set(v___x_6569_, 0, v___x_6572_);
                    v___x_6574_ = v___x_6569_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6572_);
                    v___x_6574_ = v_reuseFailAlloc_6575_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6574_;
            }
            4 => {
                if v_isShared_6587_ == 0 {
                    v___x_6589_ = v___x_6586_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
                    v___x_6589_ = v_reuseFailAlloc_6590_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(
    mut v_e_6592_: *mut leanh::LeanObject,
    mut v_a_6593_: *mut leanh::LeanObject,
    mut v_a_6594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6595_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_6592_, v_a_6593_);
    leanh::lean_dec(v_a_6593_);
    return v_res_6595_;
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond(
    mut v_e_6596_: *mut leanh::LeanObject,
    mut v_a_6597_: *mut leanh::LeanObject,
    mut v_a_6598_: *mut leanh::LeanObject,
    mut v_a_6599_: *mut leanh::LeanObject,
    mut v_a_6600_: *mut leanh::LeanObject,
    mut v_a_6601_: *mut leanh::LeanObject,
    mut v_a_6602_: *mut leanh::LeanObject,
    mut v_a_6603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6605_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_6596_, v_a_6601_);
    return v___x_6605_;
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond___boxed(
    mut v_e_6606_: *mut leanh::LeanObject,
    mut v_a_6607_: *mut leanh::LeanObject,
    mut v_a_6608_: *mut leanh::LeanObject,
    mut v_a_6609_: *mut leanh::LeanObject,
    mut v_a_6610_: *mut leanh::LeanObject,
    mut v_a_6611_: *mut leanh::LeanObject,
    mut v_a_6612_: *mut leanh::LeanObject,
    mut v_a_6613_: *mut leanh::LeanObject,
    mut v_a_6614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6615_ = l_Lean_Meta_Grind_reducePreMatchCond(
        v_e_6606_, v_a_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_,
    );
    leanh::lean_dec(v_a_6613_);
    leanh::lean_dec_ref(v_a_6612_);
    leanh::lean_dec(v_a_6611_);
    leanh::lean_dec_ref(v_a_6610_);
    leanh::lean_dec(v_a_6609_);
    leanh::lean_dec_ref(v_a_6608_);
    leanh::lean_dec(v_a_6607_);
    return v_res_6615_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_()
-> *mut leanh::LeanObject {
    let mut v___x_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6633_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_;
    v___x_6634_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_;
    v___x_6635_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_reducePreMatchCond___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6636_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6633_, v___x_6634_, v___x_6635_);
    return v___x_6636_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(
    mut v_a_6637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6638_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
    return v_res_6638_;
}
pub unsafe fn l_Lean_Meta_Grind_addPreMatchCondSimproc(
    mut v_s_6639_: *mut leanh::LeanObject,
    mut v_a_6640_: *mut leanh::LeanObject,
    mut v_a_6641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: u8 = 0;
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6643_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_;
    v___x_6644_ = 0;
    v___x_6645_ =
        l_Lean_Meta_Simp_Simprocs_add(v_s_6639_, v___x_6643_, v___x_6644_, v_a_6640_, v_a_6641_);
    return v___x_6645_;
}
pub unsafe fn l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(
    mut v_s_6646_: *mut leanh::LeanObject,
    mut v_a_6647_: *mut leanh::LeanObject,
    mut v_a_6648_: *mut leanh::LeanObject,
    mut v_a_6649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6650_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_6646_, v_a_6647_, v_a_6648_);
    leanh::lean_dec(v_a_6648_);
    leanh::lean_dec_ref(v_a_6647_);
    return v_res_6650_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__0(
    mut v_e_6651_: *mut leanh::LeanObject,
    mut v___y_6652_: *mut leanh::LeanObject,
    mut v___y_6653_: *mut leanh::LeanObject,
    mut v___y_6654_: *mut leanh::LeanObject,
    mut v___y_6655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: u8 = 0;
    let mut v_arg_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: u8 = 0;
    let mut v___x_6667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_6651_);
                v___x_6661_ = l_Lean_Expr_cleanupAnnotations(v_e_6651_);
                v___x_6662_ = l_Lean_Expr_isApp(v___x_6661_);
                if v___x_6662_ == 0 {
                    leanh::lean_dec_ref(v___x_6661_);
                    state = 1;
                    continue;
                } else {
                    v_arg_6663_ = leanh::lean_ctor_get(v___x_6661_, 1);
                    leanh::lean_inc_ref(v_arg_6663_);
                    v___x_6664_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6661_);
                    v___x_6665_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
                    v___x_6666_ = l_Lean_Expr_isConstOf(v___x_6664_, v___x_6665_);
                    leanh::lean_dec_ref(v___x_6664_);
                    if v___x_6666_ == 0 {
                        leanh::lean_dec_ref(v_arg_6663_);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_6651_);
                        v___x_6667_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_6663_);
                        v___x_6668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6668_, 0, v___x_6667_);
                        v___x_6669_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6669_, 0, v___x_6668_);
                        v___x_6670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6670_, 0, v___x_6669_);
                        return v___x_6670_;
                    }
                }
            }
            1 => {
                v___x_6658_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6658_, 0, v_e_6651_);
                v___x_6659_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6659_, 0, v___x_6658_);
                v___x_6660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6660_, 0, v___x_6659_);
                return v___x_6660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(
    mut v_e_6671_: *mut leanh::LeanObject,
    mut v___y_6672_: *mut leanh::LeanObject,
    mut v___y_6673_: *mut leanh::LeanObject,
    mut v___y_6674_: *mut leanh::LeanObject,
    mut v___y_6675_: *mut leanh::LeanObject,
    mut v___y_6676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6677_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(
        v_e_6671_,
        v___y_6672_,
        v___y_6673_,
        v___y_6674_,
        v___y_6675_,
    );
    leanh::lean_dec(v___y_6675_);
    leanh::lean_dec_ref(v___y_6674_);
    leanh::lean_dec(v___y_6673_);
    leanh::lean_dec_ref(v___y_6672_);
    return v_res_6677_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__1(
    mut v_e_6678_: *mut leanh::LeanObject,
    mut v___y_6679_: *mut leanh::LeanObject,
    mut v___y_6680_: *mut leanh::LeanObject,
    mut v___y_6681_: *mut leanh::LeanObject,
    mut v___y_6682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6684_, 0, v_e_6678_);
    v___x_6685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6685_, 0, v___x_6684_);
    return v___x_6685_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(
    mut v_e_6686_: *mut leanh::LeanObject,
    mut v___y_6687_: *mut leanh::LeanObject,
    mut v___y_6688_: *mut leanh::LeanObject,
    mut v___y_6689_: *mut leanh::LeanObject,
    mut v___y_6690_: *mut leanh::LeanObject,
    mut v___y_6691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6692_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(
        v_e_6686_,
        v___y_6687_,
        v___y_6688_,
        v___y_6689_,
        v___y_6690_,
    );
    leanh::lean_dec(v___y_6690_);
    leanh::lean_dec_ref(v___y_6689_);
    leanh::lean_dec(v___y_6688_);
    leanh::lean_dec_ref(v___y_6687_);
    return v_res_6692_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(
    mut v_00_u03b1_6693_: *mut leanh::LeanObject,
    mut v_x_6694_: *mut leanh::LeanObject,
    mut v___y_6695_: *mut leanh::LeanObject,
    mut v___y_6696_: *mut leanh::LeanObject,
    mut v___y_6697_: *mut leanh::LeanObject,
    mut v___y_6698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6700_ = leanh::lean_apply_1(v_x_6694_, leanh::lean_box(0));
    v___x_6701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
    return v___x_6701_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(
    mut v_00_u03b1_6702_: *mut leanh::LeanObject,
    mut v_x_6703_: *mut leanh::LeanObject,
    mut v___y_6704_: *mut leanh::LeanObject,
    mut v___y_6705_: *mut leanh::LeanObject,
    mut v___y_6706_: *mut leanh::LeanObject,
    mut v___y_6707_: *mut leanh::LeanObject,
    mut v___y_6708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6709_ =
        l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(
            v_00_u03b1_6702_,
            v_x_6703_,
            v___y_6704_,
            v___y_6705_,
            v___y_6706_,
            v___y_6707_,
        );
    leanh::lean_dec(v___y_6707_);
    leanh::lean_dec_ref(v___y_6706_);
    leanh::lean_dec(v___y_6705_);
    leanh::lean_dec_ref(v___y_6704_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(
    mut v_x_6710_: *mut leanh::LeanObject,
    mut v___y_6711_: *mut leanh::LeanObject,
    mut v___y_6712_: *mut leanh::LeanObject,
    mut v___y_6713_: *mut leanh::LeanObject,
    mut v___y_6714_: *mut leanh::LeanObject,
    mut v___y_6715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6722_: u8 = 0;
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6726_: u8 = 0;
    let mut v___y_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6738_: u8 = 0;
    let mut v___y_6739_: u8 = 0;
    let mut v___y_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6760_: u8 = 0;
    let mut v_cancelTk_x3f_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6762_: u8 = 0;
    let mut v_inheritedTraceOptions_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: u8 = 0;
    let mut v___x_6767_: u8 = 0;
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: u8 = 0;
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6748_ = leanh::lean_ctor_get(v___y_6714_, 0);
                v_fileMap_6749_ = leanh::lean_ctor_get(v___y_6714_, 1);
                v_options_6750_ = leanh::lean_ctor_get(v___y_6714_, 2);
                v_currRecDepth_6751_ = leanh::lean_ctor_get(v___y_6714_, 3);
                v_maxRecDepth_6752_ = leanh::lean_ctor_get(v___y_6714_, 4);
                v_ref_6753_ = leanh::lean_ctor_get(v___y_6714_, 5);
                v_currNamespace_6754_ = leanh::lean_ctor_get(v___y_6714_, 6);
                v_openDecls_6755_ = leanh::lean_ctor_get(v___y_6714_, 7);
                v_initHeartbeats_6756_ = leanh::lean_ctor_get(v___y_6714_, 8);
                v_maxHeartbeats_6757_ = leanh::lean_ctor_get(v___y_6714_, 9);
                v_quotContext_6758_ = leanh::lean_ctor_get(v___y_6714_, 10);
                v_currMacroScope_6759_ = leanh::lean_ctor_get(v___y_6714_, 11);
                v_diag_6760_ = leanh::lean_ctor_get_uint8(
                    v___y_6714_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6761_ = leanh::lean_ctor_get(v___y_6714_, 12);
                v_suppressElabErrors_6762_ = leanh::lean_ctor_get_uint8(
                    v___y_6714_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6763_ = leanh::lean_ctor_get(v___y_6714_, 13);
                if leanh::lean_obj_tag(v_cancelTk_x3f_6761_) == 1 {
                    v_val_6769_ = leanh::lean_ctor_get(v_cancelTk_x3f_6761_, 0);
                    v___x_6770_ = l_IO_CancelToken_isSet(v_val_6769_);
                    if v___x_6770_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_6710_);
                        v___x_6771_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_6772_ = leanh::lean_ctor_get(v___x_6771_, 0);
                        v_isSharedCheck_6779_ =
                            (!leanh::lean_is_exclusive(v___x_6771_)) as u8;
                        if v_isSharedCheck_6779_ == 0 {
                            v___x_6774_ = v___x_6771_;
                            v_isShared_6775_ = v_isSharedCheck_6779_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6772_);
                            leanh::lean_dec(v___x_6771_);
                            v___x_6774_ = leanh::lean_box(0);
                            v_isShared_6775_ = v_isSharedCheck_6779_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_6718_) == 0 {
                    return v___y_6718_;
                } else {
                    v_a_6719_ = leanh::lean_ctor_get(v___y_6718_, 0);
                    v_isSharedCheck_6726_ = (!leanh::lean_is_exclusive(v___y_6718_)) as u8;
                    if v_isSharedCheck_6726_ == 0 {
                        v___x_6721_ = v___y_6718_;
                        v_isShared_6722_ = v_isSharedCheck_6726_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6719_);
                        leanh::lean_dec(v___y_6718_);
                        v___x_6721_ = leanh::lean_box(0);
                        v_isShared_6722_ = v_isSharedCheck_6726_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6722_ == 0 {
                    v___x_6724_ = v___x_6721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6725_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6725_, 0, v_a_6719_);
                    v___x_6724_ = v_reuseFailAlloc_6725_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6724_;
            }
            4 => {
                v___x_6744_ = leanh::lean_unsigned_to_nat(1);
                v___x_6745_ = lean_nat_add(v___y_6728_, v___x_6744_);
                leanh::lean_inc_ref(v___y_6737_);
                leanh::lean_inc(v___y_6736_);
                leanh::lean_inc(v___y_6735_);
                leanh::lean_inc(v___y_6743_);
                leanh::lean_inc(v___y_6733_);
                leanh::lean_inc(v___y_6741_);
                leanh::lean_inc(v___y_6732_);
                leanh::lean_inc(v___y_6730_);
                leanh::lean_inc(v___y_6729_);
                leanh::lean_inc_ref(v___y_6740_);
                leanh::lean_inc_ref(v___y_6742_);
                leanh::lean_inc_ref(v___y_6734_);
                v___x_6746_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_6746_, 0, v___y_6734_);
                leanh::lean_ctor_set(v___x_6746_, 1, v___y_6742_);
                leanh::lean_ctor_set(v___x_6746_, 2, v___y_6740_);
                leanh::lean_ctor_set(v___x_6746_, 3, v___x_6745_);
                leanh::lean_ctor_set(v___x_6746_, 4, v___y_6729_);
                leanh::lean_ctor_set(v___x_6746_, 5, v___y_6731_);
                leanh::lean_ctor_set(v___x_6746_, 6, v___y_6730_);
                leanh::lean_ctor_set(v___x_6746_, 7, v___y_6732_);
                leanh::lean_ctor_set(v___x_6746_, 8, v___y_6741_);
                leanh::lean_ctor_set(v___x_6746_, 9, v___y_6733_);
                leanh::lean_ctor_set(v___x_6746_, 10, v___y_6743_);
                leanh::lean_ctor_set(v___x_6746_, 11, v___y_6735_);
                leanh::lean_ctor_set(v___x_6746_, 12, v___y_6736_);
                leanh::lean_ctor_set(v___x_6746_, 13, v___y_6737_);
                leanh::lean_ctor_set_uint8(
                    v___x_6746_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_6738_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6746_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_6739_,
                );
                leanh::lean_inc(v___y_6715_);
                leanh::lean_inc(v___y_6713_);
                leanh::lean_inc_ref(v___y_6712_);
                leanh::lean_inc(v___y_6711_);
                v___x_6747_ = leanh::lean_apply_6(
                    v_x_6710_,
                    v___y_6711_,
                    v___y_6712_,
                    v___y_6713_,
                    v___x_6746_,
                    v___y_6715_,
                    leanh::lean_box(0),
                );
                v___y_6718_ = v___x_6747_;
                state = 1;
                continue;
            }
            5 => {
                v___x_6765_ = leanh::lean_unsigned_to_nat(0);
                v___x_6766_ = lean_nat_dec_eq(v_maxRecDepth_6752_, v___x_6765_);
                if v___x_6766_ == 0 {
                    v___x_6767_ = lean_nat_dec_eq(v_currRecDepth_6751_, v_maxRecDepth_6752_);
                    if v___x_6767_ == 0 {
                        leanh::lean_inc(v_ref_6753_);
                        v___y_6728_ = v_currRecDepth_6751_;
                        v___y_6729_ = v_maxRecDepth_6752_;
                        v___y_6730_ = v_currNamespace_6754_;
                        v___y_6731_ = v_ref_6753_;
                        v___y_6732_ = v_openDecls_6755_;
                        v___y_6733_ = v_maxHeartbeats_6757_;
                        v___y_6734_ = v_fileName_6748_;
                        v___y_6735_ = v_currMacroScope_6759_;
                        v___y_6736_ = v_cancelTk_x3f_6761_;
                        v___y_6737_ = v_inheritedTraceOptions_6763_;
                        v___y_6738_ = v_diag_6760_;
                        v___y_6739_ = v_suppressElabErrors_6762_;
                        v___y_6740_ = v_options_6750_;
                        v___y_6741_ = v_initHeartbeats_6756_;
                        v___y_6742_ = v_fileMap_6749_;
                        v___y_6743_ = v_quotContext_6758_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_x_6710_);
                        leanh::lean_inc(v_ref_6753_);
                        v___x_6768_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_6753_);
                        v___y_6718_ = v___x_6768_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_ref_6753_);
                    v___y_6728_ = v_currRecDepth_6751_;
                    v___y_6729_ = v_maxRecDepth_6752_;
                    v___y_6730_ = v_currNamespace_6754_;
                    v___y_6731_ = v_ref_6753_;
                    v___y_6732_ = v_openDecls_6755_;
                    v___y_6733_ = v_maxHeartbeats_6757_;
                    v___y_6734_ = v_fileName_6748_;
                    v___y_6735_ = v_currMacroScope_6759_;
                    v___y_6736_ = v_cancelTk_x3f_6761_;
                    v___y_6737_ = v_inheritedTraceOptions_6763_;
                    v___y_6738_ = v_diag_6760_;
                    v___y_6739_ = v_suppressElabErrors_6762_;
                    v___y_6740_ = v_options_6750_;
                    v___y_6741_ = v_initHeartbeats_6756_;
                    v___y_6742_ = v_fileMap_6749_;
                    v___y_6743_ = v_quotContext_6758_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                if v_isShared_6775_ == 0 {
                    v___x_6777_ = v___x_6774_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6772_);
                    v___x_6777_ = v_reuseFailAlloc_6778_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_x_6780_: *mut leanh::LeanObject,
    mut v___y_6781_: *mut leanh::LeanObject,
    mut v___y_6782_: *mut leanh::LeanObject,
    mut v___y_6783_: *mut leanh::LeanObject,
    mut v___y_6784_: *mut leanh::LeanObject,
    mut v___y_6785_: *mut leanh::LeanObject,
    mut v___y_6786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6787_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_6780_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_, v___y_6785_);
    leanh::lean_dec(v___y_6785_);
    leanh::lean_dec_ref(v___y_6784_);
    leanh::lean_dec(v___y_6783_);
    leanh::lean_dec_ref(v___y_6782_);
    leanh::lean_dec(v___y_6781_);
    return v_res_6787_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(
    mut v_00_u03b1_6788_: *mut leanh::LeanObject,
    mut v_x_6789_: *mut leanh::LeanObject,
    mut v___y_6790_: *mut leanh::LeanObject,
    mut v___y_6791_: *mut leanh::LeanObject,
    mut v___y_6792_: *mut leanh::LeanObject,
    mut v___y_6793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6795_ = leanh::lean_apply_1(v_x_6789_, leanh::lean_box(0));
    v___x_6796_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6796_, 0, v___x_6795_);
    return v___x_6796_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_6797_: *mut leanh::LeanObject,
    mut v_x_6798_: *mut leanh::LeanObject,
    mut v___y_6799_: *mut leanh::LeanObject,
    mut v___y_6800_: *mut leanh::LeanObject,
    mut v___y_6801_: *mut leanh::LeanObject,
    mut v___y_6802_: *mut leanh::LeanObject,
    mut v___y_6803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6804_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(v_00_u03b1_6797_, v_x_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_);
    leanh::lean_dec(v___y_6802_);
    leanh::lean_dec_ref(v___y_6801_);
    leanh::lean_dec(v___y_6800_);
    leanh::lean_dec_ref(v___y_6799_);
    return v_res_6804_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(
    mut v_pre_6805_: *mut leanh::LeanObject,
    mut v_post_6806_: *mut leanh::LeanObject,
    mut v_sz_6807_: usize,
    mut v_i_6808_: usize,
    mut v_bs_6809_: *mut leanh::LeanObject,
    mut v___y_6810_: *mut leanh::LeanObject,
    mut v___y_6811_: *mut leanh::LeanObject,
    mut v___y_6812_: *mut leanh::LeanObject,
    mut v___y_6813_: *mut leanh::LeanObject,
    mut v___y_6814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6816_: u8 = 0;
    let mut v___x_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: usize = 0;
    let mut v___x_6824_: usize = 0;
    let mut v___x_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6830_: u8 = 0;
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6816_ = lean_usize_dec_lt(v_i_6808_, v_sz_6807_);
                if v___x_6816_ == 0 {
                    leanh::lean_dec_ref(v_post_6806_);
                    leanh::lean_dec_ref(v_pre_6805_);
                    v___x_6817_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6817_, 0, v_bs_6809_);
                    return v___x_6817_;
                } else {
                    v_v_6818_ = lean_array_uget_borrowed(v_bs_6809_, v_i_6808_);
                    leanh::lean_inc(v_v_6818_);
                    leanh::lean_inc_ref(v_post_6806_);
                    leanh::lean_inc_ref(v_pre_6805_);
                    v___x_6819_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6805_, v_post_6806_, v_v_6818_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_);
                    if leanh::lean_obj_tag(v___x_6819_) == 0 {
                        v_a_6820_ = leanh::lean_ctor_get(v___x_6819_, 0);
                        leanh::lean_inc(v_a_6820_);
                        leanh::lean_dec_ref_known(v___x_6819_, 1);
                        v___x_6821_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6822_ = lean_array_uset(v_bs_6809_, v_i_6808_, v___x_6821_);
                        v___x_6823_ = 1usize;
                        v___x_6824_ = lean_usize_add(v_i_6808_, v___x_6823_);
                        v___x_6825_ = lean_array_uset(v_bs_x27_6822_, v_i_6808_, v_a_6820_);
                        v_i_6808_ = v___x_6824_;
                        v_bs_6809_ = v___x_6825_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_6809_);
                        leanh::lean_dec_ref(v_post_6806_);
                        leanh::lean_dec_ref(v_pre_6805_);
                        v_a_6827_ = leanh::lean_ctor_get(v___x_6819_, 0);
                        v_isSharedCheck_6834_ =
                            (!leanh::lean_is_exclusive(v___x_6819_)) as u8;
                        if v_isSharedCheck_6834_ == 0 {
                            v___x_6829_ = v___x_6819_;
                            v_isShared_6830_ = v_isSharedCheck_6834_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6827_);
                            leanh::lean_dec(v___x_6819_);
                            v___x_6829_ = leanh::lean_box(0);
                            v_isShared_6830_ = v_isSharedCheck_6834_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6830_ == 0 {
                    v___x_6832_ = v___x_6829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6827_);
                    v___x_6832_ = v_reuseFailAlloc_6833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(
    mut v_pre_6835_: *mut leanh::LeanObject,
    mut v_post_6836_: *mut leanh::LeanObject,
    mut v_x_6837_: *mut leanh::LeanObject,
    mut v_x_6838_: *mut leanh::LeanObject,
    mut v_x_6839_: *mut leanh::LeanObject,
    mut v___y_6840_: *mut leanh::LeanObject,
    mut v___y_6841_: *mut leanh::LeanObject,
    mut v___y_6842_: *mut leanh::LeanObject,
    mut v___y_6843_: *mut leanh::LeanObject,
    mut v___y_6844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6854_: usize = 0;
    let mut v___x_6855_: usize = 0;
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6863_: u8 = 0;
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6837_) == 5 {
                    v_fn_6846_ = leanh::lean_ctor_get(v_x_6837_, 0);
                    leanh::lean_inc_ref(v_fn_6846_);
                    v_arg_6847_ = leanh::lean_ctor_get(v_x_6837_, 1);
                    leanh::lean_inc_ref(v_arg_6847_);
                    leanh::lean_dec_ref_known(v_x_6837_, 2);
                    v___x_6848_ = lean_array_set(v_x_6838_, v_x_6839_, v_arg_6847_);
                    v___x_6849_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6850_ = lean_nat_sub(v_x_6839_, v___x_6849_);
                    leanh::lean_dec(v_x_6839_);
                    v_x_6837_ = v_fn_6846_;
                    v_x_6838_ = v___x_6848_;
                    v_x_6839_ = v___x_6850_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_6839_);
                    leanh::lean_inc_ref(v_post_6836_);
                    leanh::lean_inc_ref(v_pre_6835_);
                    v___x_6852_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6835_, v_post_6836_, v_x_6837_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
                    if leanh::lean_obj_tag(v___x_6852_) == 0 {
                        v_a_6853_ = leanh::lean_ctor_get(v___x_6852_, 0);
                        leanh::lean_inc(v_a_6853_);
                        leanh::lean_dec_ref_known(v___x_6852_, 1);
                        v_sz_6854_ = lean_array_size(v_x_6838_);
                        v___x_6855_ = 0usize;
                        leanh::lean_inc_ref(v_post_6836_);
                        leanh::lean_inc_ref(v_pre_6835_);
                        v___x_6856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_6835_, v_post_6836_, v_sz_6854_, v___x_6855_, v_x_6838_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
                        if leanh::lean_obj_tag(v___x_6856_) == 0 {
                            v_a_6857_ = leanh::lean_ctor_get(v___x_6856_, 0);
                            leanh::lean_inc(v_a_6857_);
                            leanh::lean_dec_ref_known(v___x_6856_, 1);
                            v___x_6858_ = l_Lean_mkAppN(v_a_6853_, v_a_6857_);
                            leanh::lean_dec(v_a_6857_);
                            v___x_6859_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6835_, v_post_6836_, v___x_6858_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
                            return v___x_6859_;
                        } else {
                            leanh::lean_dec(v_a_6853_);
                            leanh::lean_dec_ref(v_post_6836_);
                            leanh::lean_dec_ref(v_pre_6835_);
                            v_a_6860_ = leanh::lean_ctor_get(v___x_6856_, 0);
                            v_isSharedCheck_6867_ =
                                (!leanh::lean_is_exclusive(v___x_6856_)) as u8;
                            if v_isSharedCheck_6867_ == 0 {
                                v___x_6862_ = v___x_6856_;
                                v_isShared_6863_ = v_isSharedCheck_6867_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6860_);
                                leanh::lean_dec(v___x_6856_);
                                v___x_6862_ = leanh::lean_box(0);
                                v_isShared_6863_ = v_isSharedCheck_6867_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_6838_);
                        leanh::lean_dec_ref(v_post_6836_);
                        leanh::lean_dec_ref(v_pre_6835_);
                        return v___x_6852_;
                    }
                }
            }
            1 => {
                if v_isShared_6863_ == 0 {
                    v___x_6865_ = v___x_6862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6866_, 0, v_a_6860_);
                    v___x_6865_ = v_reuseFailAlloc_6866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(
    mut v___x_6868_: *mut leanh::LeanObject,
    mut v_pre_6869_: *mut leanh::LeanObject,
    mut v_e_6870_: *mut leanh::LeanObject,
    mut v_post_6871_: *mut leanh::LeanObject,
    mut v___y_6872_: *mut leanh::LeanObject,
    mut v___y_6873_: *mut leanh::LeanObject,
    mut v___y_6874_: *mut leanh::LeanObject,
    mut v___y_6875_: *mut leanh::LeanObject,
    mut v___y_6876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6885_: u8 = 0;
    let mut v___y_6886_: u8 = 0;
    let mut v___x_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: usize = 0;
    let mut v___x_6890_: usize = 0;
    let mut v___x_6891_: u8 = 0;
    let mut v___x_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: u8 = 0;
    let mut v___y_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6901_: u8 = 0;
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: u8 = 0;
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6912_: u8 = 0;
    let mut v___y_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6914_: u8 = 0;
    let mut v___x_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: u8 = 0;
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6926_: u8 = 0;
    let mut v___y_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6932_: u8 = 0;
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: usize = 0;
    let mut v___x_6938_: usize = 0;
    let mut v___x_6939_: u8 = 0;
    let mut v___x_6940_: usize = 0;
    let mut v___x_6941_: usize = 0;
    let mut v___x_6942_: u8 = 0;
    let mut v_binderName_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6946_: u8 = 0;
    let mut v___x_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: usize = 0;
    let mut v___x_6952_: usize = 0;
    let mut v___x_6953_: u8 = 0;
    let mut v___x_6954_: usize = 0;
    let mut v___x_6955_: usize = 0;
    let mut v___x_6956_: u8 = 0;
    let mut v_declName_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6961_: u8 = 0;
    let mut v___x_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: usize = 0;
    let mut v___x_6969_: usize = 0;
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: usize = 0;
    let mut v___x_6972_: usize = 0;
    let mut v___x_6973_: u8 = 0;
    let mut v_dummy_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: usize = 0;
    let mut v___x_6985_: usize = 0;
    let mut v___x_6986_: u8 = 0;
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: usize = 0;
    let mut v___x_6996_: usize = 0;
    let mut v___x_6997_: u8 = 0;
    let mut v___x_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7012_: u8 = 0;
    let mut v_a_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7016_: u8 = 0;
    let mut v___x_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7020_: u8 = 0;
    let mut v_a_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7024_: u8 = 0;
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6921_ = l_Lean_Core_checkSystem(v___x_6868_, v___y_6875_, v___y_6876_);
                if leanh::lean_obj_tag(v___x_6921_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6921_, 1);
                    leanh::lean_inc_ref(v_pre_6869_);
                    leanh::lean_inc(v___y_6876_);
                    leanh::lean_inc_ref(v___y_6875_);
                    leanh::lean_inc(v___y_6874_);
                    leanh::lean_inc_ref(v___y_6873_);
                    leanh::lean_inc_ref(v_e_6870_);
                    v___x_6922_ = leanh::lean_apply_6(
                        v_pre_6869_,
                        v_e_6870_,
                        v___y_6873_,
                        v___y_6874_,
                        v___y_6875_,
                        v___y_6876_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6922_) == 0 {
                        v_a_6923_ = leanh::lean_ctor_get(v___x_6922_, 0);
                        v_isSharedCheck_7012_ =
                            (!leanh::lean_is_exclusive(v___x_6922_)) as u8;
                        if v_isSharedCheck_7012_ == 0 {
                            v___x_6925_ = v___x_6922_;
                            v_isShared_6926_ = v_isSharedCheck_7012_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6923_);
                            leanh::lean_dec(v___x_6922_);
                            v___x_6925_ = leanh::lean_box(0);
                            v_isShared_6926_ = v_isSharedCheck_7012_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_e_6870_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        v_a_7013_ = leanh::lean_ctor_get(v___x_6922_, 0);
                        v_isSharedCheck_7020_ =
                            (!leanh::lean_is_exclusive(v___x_6922_)) as u8;
                        if v_isSharedCheck_7020_ == 0 {
                            v___x_7015_ = v___x_6922_;
                            v_isShared_7016_ = v_isSharedCheck_7020_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7013_);
                            leanh::lean_dec(v___x_6922_);
                            v___x_7015_ = leanh::lean_box(0);
                            v_isShared_7016_ = v_isSharedCheck_7020_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_post_6871_);
                    leanh::lean_dec_ref(v_e_6870_);
                    leanh::lean_dec_ref(v_pre_6869_);
                    v_a_7021_ = leanh::lean_ctor_get(v___x_6921_, 0);
                    v_isSharedCheck_7028_ = (!leanh::lean_is_exclusive(v___x_6921_)) as u8;
                    if v_isSharedCheck_7028_ == 0 {
                        v___x_7023_ = v___x_6921_;
                        v_isShared_7024_ = v_isSharedCheck_7028_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7021_);
                        leanh::lean_dec(v___x_6921_);
                        v___x_7023_ = leanh::lean_box(0);
                        v_isShared_7024_ = v_isSharedCheck_7028_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6886_ == 0 {
                    leanh::lean_dec_ref(v___y_6884_);
                    leanh::lean_dec_ref(v___y_6879_);
                    v___x_6887_ = l_Lean_Expr_letE___override(
                        v___y_6882_,
                        v___y_6881_,
                        v___y_6880_,
                        v___y_6883_,
                        v___y_6885_,
                    );
                    v___x_6888_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6887_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    return v___x_6888_;
                } else {
                    v___x_6889_ = lean_ptr_addr(v___y_6879_);
                    leanh::lean_dec_ref(v___y_6879_);
                    v___x_6890_ = lean_ptr_addr(v___y_6883_);
                    v___x_6891_ = lean_usize_dec_eq(v___x_6889_, v___x_6890_);
                    if v___x_6891_ == 0 {
                        leanh::lean_dec_ref(v___y_6884_);
                        v___x_6892_ = l_Lean_Expr_letE___override(
                            v___y_6882_,
                            v___y_6881_,
                            v___y_6880_,
                            v___y_6883_,
                            v___y_6885_,
                        );
                        v___x_6893_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6892_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6893_;
                    } else {
                        leanh::lean_dec_ref(v___y_6883_);
                        leanh::lean_dec(v___y_6882_);
                        leanh::lean_dec_ref(v___y_6881_);
                        leanh::lean_dec_ref(v___y_6880_);
                        v___x_6894_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6884_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6894_;
                    }
                }
            }
            2 => {
                if v___y_6901_ == 0 {
                    leanh::lean_dec_ref(v___y_6900_);
                    v___x_6902_ = l_Lean_Expr_lam___override(
                        v___y_6898_,
                        v___y_6897_,
                        v___y_6896_,
                        v___y_6899_,
                    );
                    v___x_6903_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6902_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    return v___x_6903_;
                } else {
                    v___x_6904_ = l_Lean_instBEqBinderInfo_beq(v___y_6899_, v___y_6899_);
                    if v___x_6904_ == 0 {
                        leanh::lean_dec_ref(v___y_6900_);
                        v___x_6905_ = l_Lean_Expr_lam___override(
                            v___y_6898_,
                            v___y_6897_,
                            v___y_6896_,
                            v___y_6899_,
                        );
                        v___x_6906_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6905_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6906_;
                    } else {
                        leanh::lean_dec(v___y_6898_);
                        leanh::lean_dec_ref(v___y_6897_);
                        leanh::lean_dec_ref(v___y_6896_);
                        v___x_6907_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6900_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6907_;
                    }
                }
            }
            3 => {
                if v___y_6914_ == 0 {
                    leanh::lean_dec_ref(v___y_6911_);
                    v___x_6915_ = l_Lean_Expr_forallE___override(
                        v___y_6913_,
                        v___y_6910_,
                        v___y_6909_,
                        v___y_6912_,
                    );
                    v___x_6916_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6915_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    return v___x_6916_;
                } else {
                    v___x_6917_ = l_Lean_instBEqBinderInfo_beq(v___y_6912_, v___y_6912_);
                    if v___x_6917_ == 0 {
                        leanh::lean_dec_ref(v___y_6911_);
                        v___x_6918_ = l_Lean_Expr_forallE___override(
                            v___y_6913_,
                            v___y_6910_,
                            v___y_6909_,
                            v___y_6912_,
                        );
                        v___x_6919_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6918_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6919_;
                    } else {
                        leanh::lean_dec(v___y_6913_);
                        leanh::lean_dec_ref(v___y_6910_);
                        leanh::lean_dec_ref(v___y_6909_);
                        v___x_6920_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6911_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6920_;
                    }
                }
            }
            4 => match leanh::lean_obj_tag(v_a_6923_) {
                0 => {
                    leanh::lean_dec_ref(v_post_6871_);
                    leanh::lean_dec_ref(v_e_6870_);
                    leanh::lean_dec_ref(v_pre_6869_);
                    v_e_7002_ = leanh::lean_ctor_get(v_a_6923_, 0);
                    leanh::lean_inc_ref(v_e_7002_);
                    leanh::lean_dec_ref_known(v_a_6923_, 1);
                    if v_isShared_6926_ == 0 {
                        leanh::lean_ctor_set(v___x_6925_, 0, v_e_7002_);
                        v___x_7004_ = v___x_6925_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7005_, 0, v_e_7002_);
                        v___x_7004_ = v_reuseFailAlloc_7005_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_6925_);
                    leanh::lean_dec_ref(v_e_6870_);
                    v_e_7006_ = leanh::lean_ctor_get(v_a_6923_, 0);
                    leanh::lean_inc_ref(v_e_7006_);
                    leanh::lean_dec_ref_known(v_a_6923_, 1);
                    leanh::lean_inc_ref(v_post_6871_);
                    leanh::lean_inc_ref(v_pre_6869_);
                    v___x_7007_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_e_7006_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if leanh::lean_obj_tag(v___x_7007_) == 0 {
                        v_a_7008_ = leanh::lean_ctor_get(v___x_7007_, 0);
                        leanh::lean_inc(v_a_7008_);
                        leanh::lean_dec_ref_known(v___x_7007_, 1);
                        v___x_7009_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v_a_7008_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_7009_;
                    } else {
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_7007_;
                    }
                }
                _ => {
                    leanh::lean_del_object(v___x_6925_);
                    v_e_x3f_7010_ = leanh::lean_ctor_get(v_a_6923_, 0);
                    leanh::lean_inc(v_e_x3f_7010_);
                    leanh::lean_dec_ref_known(v_a_6923_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_7010_) == 0 {
                        v___y_6928_ = v_e_6870_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_e_6870_);
                        v_val_7011_ = leanh::lean_ctor_get(v_e_x3f_7010_, 0);
                        leanh::lean_inc(v_val_7011_);
                        leanh::lean_dec_ref_known(v_e_x3f_7010_, 1);
                        v___y_6928_ = v_val_7011_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match leanh::lean_obj_tag(v___y_6928_) {
                7 => {
                    v_binderName_6929_ = leanh::lean_ctor_get(v___y_6928_, 0);
                    leanh::lean_inc(v_binderName_6929_);
                    v_binderType_6930_ = leanh::lean_ctor_get(v___y_6928_, 1);
                    v_body_6931_ = leanh::lean_ctor_get(v___y_6928_, 2);
                    v_binderInfo_6932_ = leanh::lean_ctor_get_uint8(
                        v___y_6928_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6930_);
                    leanh::lean_inc_ref(v_post_6871_);
                    leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_binderType_6930_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if leanh::lean_obj_tag(v___x_6933_) == 0 {
                        v_a_6934_ = leanh::lean_ctor_get(v___x_6933_, 0);
                        leanh::lean_inc(v_a_6934_);
                        leanh::lean_dec_ref_known(v___x_6933_, 1);
                        leanh::lean_inc_ref(v_body_6931_);
                        leanh::lean_inc_ref(v_post_6871_);
                        leanh::lean_inc_ref(v_pre_6869_);
                        v___x_6935_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_body_6931_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        if leanh::lean_obj_tag(v___x_6935_) == 0 {
                            v_a_6936_ = leanh::lean_ctor_get(v___x_6935_, 0);
                            leanh::lean_inc(v_a_6936_);
                            leanh::lean_dec_ref_known(v___x_6935_, 1);
                            v___x_6937_ = lean_ptr_addr(v_binderType_6930_);
                            v___x_6938_ = lean_ptr_addr(v_a_6934_);
                            v___x_6939_ = lean_usize_dec_eq(v___x_6937_, v___x_6938_);
                            if v___x_6939_ == 0 {
                                v___y_6909_ = v_a_6936_;
                                v___y_6910_ = v_a_6934_;
                                v___y_6911_ = v___y_6928_;
                                v___y_6912_ = v_binderInfo_6932_;
                                v___y_6913_ = v_binderName_6929_;
                                v___y_6914_ = v___x_6939_;
                                state = 3;
                                continue;
                            } else {
                                v___x_6940_ = lean_ptr_addr(v_body_6931_);
                                v___x_6941_ = lean_ptr_addr(v_a_6936_);
                                v___x_6942_ = lean_usize_dec_eq(v___x_6940_, v___x_6941_);
                                v___y_6909_ = v_a_6936_;
                                v___y_6910_ = v_a_6934_;
                                v___y_6911_ = v___y_6928_;
                                v___y_6912_ = v_binderInfo_6932_;
                                v___y_6913_ = v_binderName_6929_;
                                v___y_6914_ = v___x_6942_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6934_);
                            leanh::lean_dec_ref_known(v___y_6928_, 3);
                            leanh::lean_dec(v_binderName_6929_);
                            leanh::lean_dec_ref(v_post_6871_);
                            leanh::lean_dec_ref(v_pre_6869_);
                            return v___x_6935_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6928_, 3);
                        leanh::lean_dec(v_binderName_6929_);
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6933_;
                    }
                }
                6 => {
                    v_binderName_6943_ = leanh::lean_ctor_get(v___y_6928_, 0);
                    leanh::lean_inc(v_binderName_6943_);
                    v_binderType_6944_ = leanh::lean_ctor_get(v___y_6928_, 1);
                    v_body_6945_ = leanh::lean_ctor_get(v___y_6928_, 2);
                    v_binderInfo_6946_ = leanh::lean_ctor_get_uint8(
                        v___y_6928_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6944_);
                    leanh::lean_inc_ref(v_post_6871_);
                    leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6947_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_binderType_6944_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if leanh::lean_obj_tag(v___x_6947_) == 0 {
                        v_a_6948_ = leanh::lean_ctor_get(v___x_6947_, 0);
                        leanh::lean_inc(v_a_6948_);
                        leanh::lean_dec_ref_known(v___x_6947_, 1);
                        leanh::lean_inc_ref(v_body_6945_);
                        leanh::lean_inc_ref(v_post_6871_);
                        leanh::lean_inc_ref(v_pre_6869_);
                        v___x_6949_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_body_6945_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        if leanh::lean_obj_tag(v___x_6949_) == 0 {
                            v_a_6950_ = leanh::lean_ctor_get(v___x_6949_, 0);
                            leanh::lean_inc(v_a_6950_);
                            leanh::lean_dec_ref_known(v___x_6949_, 1);
                            v___x_6951_ = lean_ptr_addr(v_binderType_6944_);
                            v___x_6952_ = lean_ptr_addr(v_a_6948_);
                            v___x_6953_ = lean_usize_dec_eq(v___x_6951_, v___x_6952_);
                            if v___x_6953_ == 0 {
                                v___y_6896_ = v_a_6950_;
                                v___y_6897_ = v_a_6948_;
                                v___y_6898_ = v_binderName_6943_;
                                v___y_6899_ = v_binderInfo_6946_;
                                v___y_6900_ = v___y_6928_;
                                v___y_6901_ = v___x_6953_;
                                state = 2;
                                continue;
                            } else {
                                v___x_6954_ = lean_ptr_addr(v_body_6945_);
                                v___x_6955_ = lean_ptr_addr(v_a_6950_);
                                v___x_6956_ = lean_usize_dec_eq(v___x_6954_, v___x_6955_);
                                v___y_6896_ = v_a_6950_;
                                v___y_6897_ = v_a_6948_;
                                v___y_6898_ = v_binderName_6943_;
                                v___y_6899_ = v_binderInfo_6946_;
                                v___y_6900_ = v___y_6928_;
                                v___y_6901_ = v___x_6956_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6948_);
                            leanh::lean_dec_ref_known(v___y_6928_, 3);
                            leanh::lean_dec(v_binderName_6943_);
                            leanh::lean_dec_ref(v_post_6871_);
                            leanh::lean_dec_ref(v_pre_6869_);
                            return v___x_6949_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6928_, 3);
                        leanh::lean_dec(v_binderName_6943_);
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6947_;
                    }
                }
                8 => {
                    v_declName_6957_ = leanh::lean_ctor_get(v___y_6928_, 0);
                    leanh::lean_inc(v_declName_6957_);
                    v_type_6958_ = leanh::lean_ctor_get(v___y_6928_, 1);
                    v_value_6959_ = leanh::lean_ctor_get(v___y_6928_, 2);
                    v_body_6960_ = leanh::lean_ctor_get(v___y_6928_, 3);
                    leanh::lean_inc_ref(v_body_6960_);
                    v_nondep_6961_ = leanh::lean_ctor_get_uint8(
                        v___y_6928_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_6958_);
                    leanh::lean_inc_ref(v_post_6871_);
                    leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6962_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_type_6958_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if leanh::lean_obj_tag(v___x_6962_) == 0 {
                        v_a_6963_ = leanh::lean_ctor_get(v___x_6962_, 0);
                        leanh::lean_inc(v_a_6963_);
                        leanh::lean_dec_ref_known(v___x_6962_, 1);
                        leanh::lean_inc_ref(v_value_6959_);
                        leanh::lean_inc_ref(v_post_6871_);
                        leanh::lean_inc_ref(v_pre_6869_);
                        v___x_6964_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_value_6959_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        if leanh::lean_obj_tag(v___x_6964_) == 0 {
                            v_a_6965_ = leanh::lean_ctor_get(v___x_6964_, 0);
                            leanh::lean_inc(v_a_6965_);
                            leanh::lean_dec_ref_known(v___x_6964_, 1);
                            leanh::lean_inc_ref(v_body_6960_);
                            leanh::lean_inc_ref(v_post_6871_);
                            leanh::lean_inc_ref(v_pre_6869_);
                            v___x_6966_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_body_6960_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            if leanh::lean_obj_tag(v___x_6966_) == 0 {
                                v_a_6967_ = leanh::lean_ctor_get(v___x_6966_, 0);
                                leanh::lean_inc(v_a_6967_);
                                leanh::lean_dec_ref_known(v___x_6966_, 1);
                                v___x_6968_ = lean_ptr_addr(v_type_6958_);
                                v___x_6969_ = lean_ptr_addr(v_a_6963_);
                                v___x_6970_ = lean_usize_dec_eq(v___x_6968_, v___x_6969_);
                                if v___x_6970_ == 0 {
                                    v___y_6879_ = v_body_6960_;
                                    v___y_6880_ = v_a_6965_;
                                    v___y_6881_ = v_a_6963_;
                                    v___y_6882_ = v_declName_6957_;
                                    v___y_6883_ = v_a_6967_;
                                    v___y_6884_ = v___y_6928_;
                                    v___y_6885_ = v_nondep_6961_;
                                    v___y_6886_ = v___x_6970_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_6971_ = lean_ptr_addr(v_value_6959_);
                                    v___x_6972_ = lean_ptr_addr(v_a_6965_);
                                    v___x_6973_ = lean_usize_dec_eq(v___x_6971_, v___x_6972_);
                                    v___y_6879_ = v_body_6960_;
                                    v___y_6880_ = v_a_6965_;
                                    v___y_6881_ = v_a_6963_;
                                    v___y_6882_ = v_declName_6957_;
                                    v___y_6883_ = v_a_6967_;
                                    v___y_6884_ = v___y_6928_;
                                    v___y_6885_ = v_nondep_6961_;
                                    v___y_6886_ = v___x_6973_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_6965_);
                                leanh::lean_dec(v_a_6963_);
                                leanh::lean_dec_ref(v_body_6960_);
                                leanh::lean_dec_ref_known(v___y_6928_, 4);
                                leanh::lean_dec(v_declName_6957_);
                                leanh::lean_dec_ref(v_post_6871_);
                                leanh::lean_dec_ref(v_pre_6869_);
                                return v___x_6966_;
                            }
                        } else {
                            leanh::lean_dec(v_a_6963_);
                            leanh::lean_dec_ref(v_body_6960_);
                            leanh::lean_dec_ref_known(v___y_6928_, 4);
                            leanh::lean_dec(v_declName_6957_);
                            leanh::lean_dec_ref(v_post_6871_);
                            leanh::lean_dec_ref(v_pre_6869_);
                            return v___x_6964_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_6960_);
                        leanh::lean_dec(v_declName_6957_);
                        leanh::lean_dec_ref_known(v___y_6928_, 4);
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6962_;
                    }
                }
                5 => {
                    v_dummy_6974_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_6975_ = l_Lean_Expr_getAppNumArgs(v___y_6928_);
                    leanh::lean_inc(v_nargs_6975_);
                    v___x_6976_ = lean_mk_array(v_nargs_6975_, v_dummy_6974_);
                    v___x_6977_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6978_ = lean_nat_sub(v_nargs_6975_, v___x_6977_);
                    leanh::lean_dec(v_nargs_6975_);
                    v___x_6979_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_6869_, v_post_6871_, v___y_6928_, v___x_6976_, v___x_6978_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    return v___x_6979_;
                }
                10 => {
                    v_data_6980_ = leanh::lean_ctor_get(v___y_6928_, 0);
                    v_expr_6981_ = leanh::lean_ctor_get(v___y_6928_, 1);
                    leanh::lean_inc_ref(v_expr_6981_);
                    leanh::lean_inc_ref(v_post_6871_);
                    leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6982_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_expr_6981_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if leanh::lean_obj_tag(v___x_6982_) == 0 {
                        v_a_6983_ = leanh::lean_ctor_get(v___x_6982_, 0);
                        leanh::lean_inc(v_a_6983_);
                        leanh::lean_dec_ref_known(v___x_6982_, 1);
                        v___x_6984_ = lean_ptr_addr(v_expr_6981_);
                        v___x_6985_ = lean_ptr_addr(v_a_6983_);
                        v___x_6986_ = lean_usize_dec_eq(v___x_6984_, v___x_6985_);
                        if v___x_6986_ == 0 {
                            leanh::lean_inc(v_data_6980_);
                            leanh::lean_dec_ref_known(v___y_6928_, 2);
                            v___x_6987_ = l_Lean_Expr_mdata___override(v_data_6980_, v_a_6983_);
                            v___x_6988_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6987_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_6988_;
                        } else {
                            leanh::lean_dec(v_a_6983_);
                            v___x_6989_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6928_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_6989_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6928_, 2);
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6982_;
                    }
                }
                11 => {
                    v_typeName_6990_ = leanh::lean_ctor_get(v___y_6928_, 0);
                    v_idx_6991_ = leanh::lean_ctor_get(v___y_6928_, 1);
                    v_struct_6992_ = leanh::lean_ctor_get(v___y_6928_, 2);
                    leanh::lean_inc_ref(v_struct_6992_);
                    leanh::lean_inc_ref(v_post_6871_);
                    leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6993_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_struct_6992_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if leanh::lean_obj_tag(v___x_6993_) == 0 {
                        v_a_6994_ = leanh::lean_ctor_get(v___x_6993_, 0);
                        leanh::lean_inc(v_a_6994_);
                        leanh::lean_dec_ref_known(v___x_6993_, 1);
                        v___x_6995_ = lean_ptr_addr(v_struct_6992_);
                        v___x_6996_ = lean_ptr_addr(v_a_6994_);
                        v___x_6997_ = lean_usize_dec_eq(v___x_6995_, v___x_6996_);
                        if v___x_6997_ == 0 {
                            leanh::lean_inc(v_idx_6991_);
                            leanh::lean_inc(v_typeName_6990_);
                            leanh::lean_dec_ref_known(v___y_6928_, 3);
                            v___x_6998_ = l_Lean_Expr_proj___override(
                                v_typeName_6990_,
                                v_idx_6991_,
                                v_a_6994_,
                            );
                            v___x_6999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6998_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_6999_;
                        } else {
                            leanh::lean_dec(v_a_6994_);
                            v___x_7000_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6928_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_7000_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___y_6928_, 3);
                        leanh::lean_dec_ref(v_post_6871_);
                        leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6993_;
                    }
                }
                _ => {
                    v___x_7001_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6928_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    return v___x_7001_;
                }
            },
            6 => {
                return v___x_7004_;
            }
            7 => {
                if v_isShared_7016_ == 0 {
                    v___x_7018_ = v___x_7015_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7019_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7019_, 0, v_a_7013_);
                    v___x_7018_ = v_reuseFailAlloc_7019_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7018_;
            }
            9 => {
                if v_isShared_7024_ == 0 {
                    v___x_7026_ = v___x_7023_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 0, v_a_7021_);
                    v___x_7026_ = v_reuseFailAlloc_7027_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(
    mut v___x_7029_: *mut leanh::LeanObject,
    mut v_pre_7030_: *mut leanh::LeanObject,
    mut v_e_7031_: *mut leanh::LeanObject,
    mut v_post_7032_: *mut leanh::LeanObject,
    mut v___y_7033_: *mut leanh::LeanObject,
    mut v___y_7034_: *mut leanh::LeanObject,
    mut v___y_7035_: *mut leanh::LeanObject,
    mut v___y_7036_: *mut leanh::LeanObject,
    mut v___y_7037_: *mut leanh::LeanObject,
    mut v___y_7038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7039_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_7029_, v_pre_7030_, v_e_7031_, v_post_7032_, v___y_7033_, v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_);
    leanh::lean_dec(v___y_7037_);
    leanh::lean_dec_ref(v___y_7036_);
    leanh::lean_dec(v___y_7035_);
    leanh::lean_dec_ref(v___y_7034_);
    leanh::lean_dec(v___y_7033_);
    return v_res_7039_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(
    mut v_pre_7040_: *mut leanh::LeanObject,
    mut v_post_7041_: *mut leanh::LeanObject,
    mut v_e_7042_: *mut leanh::LeanObject,
    mut v_a_7043_: *mut leanh::LeanObject,
    mut v___y_7044_: *mut leanh::LeanObject,
    mut v___y_7045_: *mut leanh::LeanObject,
    mut v___y_7046_: *mut leanh::LeanObject,
    mut v___y_7047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7054_: u8 = 0;
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7064_: u8 = 0;
    let mut v___x_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7068_: u8 = 0;
    let mut v_unused_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7073_: u8 = 0;
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7077_: u8 = 0;
    let mut v_val_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7082_: u8 = 0;
    let mut v_a_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7086_: u8 = 0;
    let mut v___x_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_7043_);
                v___x_7049_ = leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_7049_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7049_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7049_, 2, v_a_7043_);
                v___x_7050_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(leanh::lean_box(0), v___x_7049_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                if leanh::lean_obj_tag(v___x_7050_) == 0 {
                    v_a_7051_ = leanh::lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7082_ = (!leanh::lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7082_ == 0 {
                        v___x_7053_ = v___x_7050_;
                        v_isShared_7054_ = v_isSharedCheck_7082_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7051_);
                        leanh::lean_dec(v___x_7050_);
                        v___x_7053_ = leanh::lean_box(0);
                        v_isShared_7054_ = v_isSharedCheck_7082_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7042_);
                    leanh::lean_dec_ref(v_post_7041_);
                    leanh::lean_dec_ref(v_pre_7040_);
                    v_a_7083_ = leanh::lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7090_ = (!leanh::lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7090_ == 0 {
                        v___x_7085_ = v___x_7050_;
                        v_isShared_7086_ = v_isSharedCheck_7090_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7083_);
                        leanh::lean_dec(v___x_7050_);
                        v___x_7085_ = leanh::lean_box(0);
                        v_isShared_7086_ = v_isSharedCheck_7090_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_7051_, v_e_7042_);
                leanh::lean_dec(v_a_7051_);
                if leanh::lean_obj_tag(v___x_7055_) == 0 {
                    leanh::lean_del_object(v___x_7053_);
                    v___x_7056_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0;
                    leanh::lean_inc_ref(v_e_7042_);
                    v___f_7057_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 10, 4);
                    leanh::lean_closure_set(v___f_7057_, 0, v___x_7056_);
                    leanh::lean_closure_set(v___f_7057_, 1, v_pre_7040_);
                    leanh::lean_closure_set(v___f_7057_, 2, v_e_7042_);
                    leanh::lean_closure_set(v___f_7057_, 3, v_post_7041_);
                    v___x_7058_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_7057_, v_a_7043_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                    if leanh::lean_obj_tag(v___x_7058_) == 0 {
                        v_a_7059_ = leanh::lean_ctor_get(v___x_7058_, 0);
                        leanh::lean_inc_n(v_a_7059_, 2);
                        leanh::lean_dec_ref_known(v___x_7058_, 1);
                        leanh::lean_inc(v_a_7043_);
                        v___f_7060_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_7060_, 0, v_a_7043_);
                        leanh::lean_closure_set(v___f_7060_, 1, v_e_7042_);
                        leanh::lean_closure_set(v___f_7060_, 2, v_a_7059_);
                        v___x_7061_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(leanh::lean_box(0), v___f_7060_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                        if leanh::lean_obj_tag(v___x_7061_) == 0 {
                            v_isSharedCheck_7068_ =
                                (!leanh::lean_is_exclusive(v___x_7061_)) as u8;
                            if v_isSharedCheck_7068_ == 0 {
                                v_unused_7069_ = leanh::lean_ctor_get(v___x_7061_, 0);
                                leanh::lean_dec(v_unused_7069_);
                                v___x_7063_ = v___x_7061_;
                                v_isShared_7064_ = v_isSharedCheck_7068_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7061_);
                                v___x_7063_ = leanh::lean_box(0);
                                v_isShared_7064_ = v_isSharedCheck_7068_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7059_);
                            v_a_7070_ = leanh::lean_ctor_get(v___x_7061_, 0);
                            v_isSharedCheck_7077_ =
                                (!leanh::lean_is_exclusive(v___x_7061_)) as u8;
                            if v_isSharedCheck_7077_ == 0 {
                                v___x_7072_ = v___x_7061_;
                                v_isShared_7073_ = v_isSharedCheck_7077_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7070_);
                                leanh::lean_dec(v___x_7061_);
                                v___x_7072_ = leanh::lean_box(0);
                                v_isShared_7073_ = v_isSharedCheck_7077_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7042_);
                        return v___x_7058_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7042_);
                    leanh::lean_dec_ref(v_post_7041_);
                    leanh::lean_dec_ref(v_pre_7040_);
                    v_val_7078_ = leanh::lean_ctor_get(v___x_7055_, 0);
                    leanh::lean_inc(v_val_7078_);
                    leanh::lean_dec_ref_known(v___x_7055_, 1);
                    if v_isShared_7054_ == 0 {
                        leanh::lean_ctor_set(v___x_7053_, 0, v_val_7078_);
                        v___x_7080_ = v___x_7053_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7081_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_val_7078_);
                        v___x_7080_ = v_reuseFailAlloc_7081_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7064_ == 0 {
                    leanh::lean_ctor_set(v___x_7063_, 0, v_a_7059_);
                    v___x_7066_ = v___x_7063_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7067_, 0, v_a_7059_);
                    v___x_7066_ = v_reuseFailAlloc_7067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7066_;
            }
            4 => {
                if v_isShared_7073_ == 0 {
                    v___x_7075_ = v___x_7072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7076_, 0, v_a_7070_);
                    v___x_7075_ = v_reuseFailAlloc_7076_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7075_;
            }
            6 => {
                return v___x_7080_;
            }
            7 => {
                if v_isShared_7086_ == 0 {
                    v___x_7088_ = v___x_7085_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7089_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 0, v_a_7083_);
                    v___x_7088_ = v_reuseFailAlloc_7089_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(
    mut v_pre_7091_: *mut leanh::LeanObject,
    mut v_post_7092_: *mut leanh::LeanObject,
    mut v_e_7093_: *mut leanh::LeanObject,
    mut v_a_7094_: *mut leanh::LeanObject,
    mut v___y_7095_: *mut leanh::LeanObject,
    mut v___y_7096_: *mut leanh::LeanObject,
    mut v___y_7097_: *mut leanh::LeanObject,
    mut v___y_7098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7104_: u8 = 0;
    let mut v_e_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7119_: u8 = 0;
    let mut v_a_7120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v___x_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_post_7092_);
                leanh::lean_inc(v___y_7098_);
                leanh::lean_inc_ref(v___y_7097_);
                leanh::lean_inc(v___y_7096_);
                leanh::lean_inc_ref(v___y_7095_);
                leanh::lean_inc_ref(v_e_7093_);
                v___x_7100_ = leanh::lean_apply_6(
                    v_post_7092_,
                    v_e_7093_,
                    v___y_7095_,
                    v___y_7096_,
                    v___y_7097_,
                    v___y_7098_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_7100_) == 0 {
                    v_a_7101_ = leanh::lean_ctor_get(v___x_7100_, 0);
                    v_isSharedCheck_7119_ = (!leanh::lean_is_exclusive(v___x_7100_)) as u8;
                    if v_isSharedCheck_7119_ == 0 {
                        v___x_7103_ = v___x_7100_;
                        v_isShared_7104_ = v_isSharedCheck_7119_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7101_);
                        leanh::lean_dec(v___x_7100_);
                        v___x_7103_ = leanh::lean_box(0);
                        v_isShared_7104_ = v_isSharedCheck_7119_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7093_);
                    leanh::lean_dec_ref(v_post_7092_);
                    leanh::lean_dec_ref(v_pre_7091_);
                    v_a_7120_ = leanh::lean_ctor_get(v___x_7100_, 0);
                    v_isSharedCheck_7127_ = (!leanh::lean_is_exclusive(v___x_7100_)) as u8;
                    if v_isSharedCheck_7127_ == 0 {
                        v___x_7122_ = v___x_7100_;
                        v_isShared_7123_ = v_isSharedCheck_7127_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7120_);
                        leanh::lean_dec(v___x_7100_);
                        v___x_7122_ = leanh::lean_box(0);
                        v_isShared_7123_ = v_isSharedCheck_7127_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_a_7101_) {
                0 => {
                    leanh::lean_dec_ref(v_e_7093_);
                    leanh::lean_dec_ref(v_post_7092_);
                    leanh::lean_dec_ref(v_pre_7091_);
                    v_e_7105_ = leanh::lean_ctor_get(v_a_7101_, 0);
                    leanh::lean_inc_ref(v_e_7105_);
                    leanh::lean_dec_ref_known(v_a_7101_, 1);
                    if v_isShared_7104_ == 0 {
                        leanh::lean_ctor_set(v___x_7103_, 0, v_e_7105_);
                        v___x_7107_ = v___x_7103_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_e_7105_);
                        v___x_7107_ = v_reuseFailAlloc_7108_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_del_object(v___x_7103_);
                    leanh::lean_dec_ref(v_e_7093_);
                    v_e_7109_ = leanh::lean_ctor_get(v_a_7101_, 0);
                    leanh::lean_inc_ref(v_e_7109_);
                    leanh::lean_dec_ref_known(v_a_7101_, 1);
                    v___x_7110_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_7091_, v_post_7092_, v_e_7109_, v_a_7094_, v___y_7095_, v___y_7096_, v___y_7097_, v___y_7098_);
                    return v___x_7110_;
                }
                _ => {
                    leanh::lean_dec_ref(v_post_7092_);
                    leanh::lean_dec_ref(v_pre_7091_);
                    v_e_x3f_7111_ = leanh::lean_ctor_get(v_a_7101_, 0);
                    leanh::lean_inc(v_e_x3f_7111_);
                    leanh::lean_dec_ref_known(v_a_7101_, 1);
                    if leanh::lean_obj_tag(v_e_x3f_7111_) == 0 {
                        if v_isShared_7104_ == 0 {
                            leanh::lean_ctor_set(v___x_7103_, 0, v_e_7093_);
                            v___x_7113_ = v___x_7103_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7114_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7114_, 0, v_e_7093_);
                            v___x_7113_ = v_reuseFailAlloc_7114_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7093_);
                        v_val_7115_ = leanh::lean_ctor_get(v_e_x3f_7111_, 0);
                        leanh::lean_inc(v_val_7115_);
                        leanh::lean_dec_ref_known(v_e_x3f_7111_, 1);
                        if v_isShared_7104_ == 0 {
                            leanh::lean_ctor_set(v___x_7103_, 0, v_val_7115_);
                            v___x_7117_ = v___x_7103_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7118_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7118_, 0, v_val_7115_);
                            v___x_7117_ = v_reuseFailAlloc_7118_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_7107_;
            }
            3 => {
                return v___x_7113_;
            }
            4 => {
                return v___x_7117_;
            }
            5 => {
                if v_isShared_7123_ == 0 {
                    v___x_7125_ = v___x_7122_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7126_, 0, v_a_7120_);
                    v___x_7125_ = v_reuseFailAlloc_7126_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(
    mut v_pre_7128_: *mut leanh::LeanObject,
    mut v_post_7129_: *mut leanh::LeanObject,
    mut v_e_7130_: *mut leanh::LeanObject,
    mut v_a_7131_: *mut leanh::LeanObject,
    mut v___y_7132_: *mut leanh::LeanObject,
    mut v___y_7133_: *mut leanh::LeanObject,
    mut v___y_7134_: *mut leanh::LeanObject,
    mut v___y_7135_: *mut leanh::LeanObject,
    mut v___y_7136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7137_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_7128_, v_post_7129_, v_e_7130_, v_a_7131_, v___y_7132_, v___y_7133_, v___y_7134_, v___y_7135_);
    leanh::lean_dec(v___y_7135_);
    leanh::lean_dec_ref(v___y_7134_);
    leanh::lean_dec(v___y_7133_);
    leanh::lean_dec_ref(v___y_7132_);
    leanh::lean_dec(v_a_7131_);
    return v_res_7137_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(
    mut v_pre_7138_: *mut leanh::LeanObject,
    mut v_post_7139_: *mut leanh::LeanObject,
    mut v_sz_7140_: *mut leanh::LeanObject,
    mut v_i_7141_: *mut leanh::LeanObject,
    mut v_bs_7142_: *mut leanh::LeanObject,
    mut v___y_7143_: *mut leanh::LeanObject,
    mut v___y_7144_: *mut leanh::LeanObject,
    mut v___y_7145_: *mut leanh::LeanObject,
    mut v___y_7146_: *mut leanh::LeanObject,
    mut v___y_7147_: *mut leanh::LeanObject,
    mut v___y_7148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7149_: usize = 0;
    let mut v_i_boxed_7150_: usize = 0;
    let mut v_res_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7149_ = leanh::lean_unbox_usize(v_sz_7140_);
    leanh::lean_dec(v_sz_7140_);
    v_i_boxed_7150_ = leanh::lean_unbox_usize(v_i_7141_);
    leanh::lean_dec(v_i_7141_);
    v_res_7151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_7138_, v_post_7139_, v_sz_boxed_7149_, v_i_boxed_7150_, v_bs_7142_, v___y_7143_, v___y_7144_, v___y_7145_, v___y_7146_, v___y_7147_);
    leanh::lean_dec(v___y_7147_);
    leanh::lean_dec_ref(v___y_7146_);
    leanh::lean_dec(v___y_7145_);
    leanh::lean_dec_ref(v___y_7144_);
    leanh::lean_dec(v___y_7143_);
    return v_res_7151_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(
    mut v_pre_7152_: *mut leanh::LeanObject,
    mut v_post_7153_: *mut leanh::LeanObject,
    mut v_x_7154_: *mut leanh::LeanObject,
    mut v_x_7155_: *mut leanh::LeanObject,
    mut v_x_7156_: *mut leanh::LeanObject,
    mut v___y_7157_: *mut leanh::LeanObject,
    mut v___y_7158_: *mut leanh::LeanObject,
    mut v___y_7159_: *mut leanh::LeanObject,
    mut v___y_7160_: *mut leanh::LeanObject,
    mut v___y_7161_: *mut leanh::LeanObject,
    mut v___y_7162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7163_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_7152_, v_post_7153_, v_x_7154_, v_x_7155_, v_x_7156_, v___y_7157_, v___y_7158_, v___y_7159_, v___y_7160_, v___y_7161_);
    leanh::lean_dec(v___y_7161_);
    leanh::lean_dec_ref(v___y_7160_);
    leanh::lean_dec(v___y_7159_);
    leanh::lean_dec_ref(v___y_7158_);
    leanh::lean_dec(v___y_7157_);
    return v_res_7163_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(
    mut v_pre_7164_: *mut leanh::LeanObject,
    mut v_post_7165_: *mut leanh::LeanObject,
    mut v_e_7166_: *mut leanh::LeanObject,
    mut v_a_7167_: *mut leanh::LeanObject,
    mut v___y_7168_: *mut leanh::LeanObject,
    mut v___y_7169_: *mut leanh::LeanObject,
    mut v___y_7170_: *mut leanh::LeanObject,
    mut v___y_7171_: *mut leanh::LeanObject,
    mut v___y_7172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_7164_, v_post_7165_, v_e_7166_, v_a_7167_, v___y_7168_, v___y_7169_, v___y_7170_, v___y_7171_);
    leanh::lean_dec(v___y_7171_);
    leanh::lean_dec_ref(v___y_7170_);
    leanh::lean_dec(v___y_7169_);
    leanh::lean_dec_ref(v___y_7168_);
    leanh::lean_dec(v_a_7167_);
    return v_res_7173_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(
    mut v_input_7174_: *mut leanh::LeanObject,
    mut v_pre_7175_: *mut leanh::LeanObject,
    mut v_post_7176_: *mut leanh::LeanObject,
    mut v___y_7177_: *mut leanh::LeanObject,
    mut v___y_7178_: *mut leanh::LeanObject,
    mut v___y_7179_: *mut leanh::LeanObject,
    mut v___y_7180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7191_: u8 = 0;
    let mut v___x_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7195_: u8 = 0;
    let mut v_unused_7196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7182_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
                v___x_7183_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(leanh::lean_box(0), v___x_7182_, v___y_7177_, v___y_7178_, v___y_7179_, v___y_7180_);
                v_a_7184_ = leanh::lean_ctor_get(v___x_7183_, 0);
                leanh::lean_inc(v_a_7184_);
                leanh::lean_dec_ref(v___x_7183_);
                v___x_7185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_7175_, v_post_7176_, v_input_7174_, v_a_7184_, v___y_7177_, v___y_7178_, v___y_7179_, v___y_7180_);
                if leanh::lean_obj_tag(v___x_7185_) == 0 {
                    v_a_7186_ = leanh::lean_ctor_get(v___x_7185_, 0);
                    leanh::lean_inc(v_a_7186_);
                    leanh::lean_dec_ref_known(v___x_7185_, 1);
                    v___x_7187_ = leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___x_7187_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7187_, 1, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7187_, 2, v_a_7184_);
                    v___x_7188_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(leanh::lean_box(0), v___x_7187_, v___y_7177_, v___y_7178_, v___y_7179_, v___y_7180_);
                    v_isSharedCheck_7195_ = (!leanh::lean_is_exclusive(v___x_7188_)) as u8;
                    if v_isSharedCheck_7195_ == 0 {
                        v_unused_7196_ = leanh::lean_ctor_get(v___x_7188_, 0);
                        leanh::lean_dec(v_unused_7196_);
                        v___x_7190_ = v___x_7188_;
                        v_isShared_7191_ = v_isSharedCheck_7195_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7188_);
                        v___x_7190_ = leanh::lean_box(0);
                        v_isShared_7191_ = v_isSharedCheck_7195_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7184_);
                    return v___x_7185_;
                }
            }
            1 => {
                if v_isShared_7191_ == 0 {
                    leanh::lean_ctor_set(v___x_7190_, 0, v_a_7186_);
                    v___x_7193_ = v___x_7190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 0, v_a_7186_);
                    v___x_7193_ = v_reuseFailAlloc_7194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(
    mut v_input_7197_: *mut leanh::LeanObject,
    mut v_pre_7198_: *mut leanh::LeanObject,
    mut v_post_7199_: *mut leanh::LeanObject,
    mut v___y_7200_: *mut leanh::LeanObject,
    mut v___y_7201_: *mut leanh::LeanObject,
    mut v___y_7202_: *mut leanh::LeanObject,
    mut v___y_7203_: *mut leanh::LeanObject,
    mut v___y_7204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7205_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(
        v_input_7197_,
        v_pre_7198_,
        v_post_7199_,
        v___y_7200_,
        v___y_7201_,
        v___y_7202_,
        v___y_7203_,
    );
    leanh::lean_dec(v___y_7203_);
    leanh::lean_dec_ref(v___y_7202_);
    leanh::lean_dec(v___y_7201_);
    leanh::lean_dec_ref(v___y_7200_);
    return v_res_7205_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond(
    mut v_e_7209_: *mut leanh::LeanObject,
    mut v_a_7210_: *mut leanh::LeanObject,
    mut v_a_7211_: *mut leanh::LeanObject,
    mut v_a_7212_: *mut leanh::LeanObject,
    mut v_a_7213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v_pre_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7233_: u8 = 0;
    let mut v___x_7234_: u8 = 0;
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7243_: u8 = 0;
    let mut v_a_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7247_: u8 = 0;
    let mut v___x_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7251_: u8 = 0;
    let mut v_a_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7255_: u8 = 0;
    let mut v___x_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7259_: u8 = 0;
    let mut v_a_7260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7263_: u8 = 0;
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7267_: u8 = 0;
    let mut v_isSharedCheck_7268_: u8 = 0;
    let mut v_unused_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7215_ = l_Lean_Meta_Grind_replacePreMatchCond___closed__0;
                v___x_7216_ = lean_find_expr(v___x_7215_, v_e_7209_);
                if leanh::lean_obj_tag(v___x_7216_) == 0 {
                    v___x_7217_ = 1;
                    v___x_7218_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_7218_, 0, v_e_7209_);
                    leanh::lean_ctor_set(v___x_7218_, 1, v___x_7216_);
                    leanh::lean_ctor_set_uint8(
                        v___x_7218_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_7217_,
                    );
                    v___x_7219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7219_, 0, v___x_7218_);
                    return v___x_7219_;
                } else {
                    v_isSharedCheck_7268_ = (!leanh::lean_is_exclusive(v___x_7216_)) as u8;
                    if v_isSharedCheck_7268_ == 0 {
                        v_unused_7269_ = leanh::lean_ctor_get(v___x_7216_, 0);
                        leanh::lean_dec(v_unused_7269_);
                        v___x_7221_ = v___x_7216_;
                        v_isShared_7222_ = v_isSharedCheck_7268_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7216_);
                        v___x_7221_ = leanh::lean_box(0);
                        v_isShared_7222_ = v_isSharedCheck_7268_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pre_7223_ = l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
                v___f_7224_ = l_Lean_Meta_Grind_replacePreMatchCond___closed__2;
                leanh::lean_inc_ref(v_e_7209_);
                v___x_7225_ =
                    l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(
                        v_e_7209_,
                        v_pre_7223_,
                        v___f_7224_,
                        v_a_7210_,
                        v_a_7211_,
                        v_a_7212_,
                        v_a_7213_,
                    );
                if leanh::lean_obj_tag(v___x_7225_) == 0 {
                    v_a_7226_ = leanh::lean_ctor_get(v___x_7225_, 0);
                    leanh::lean_inc_n(v_a_7226_, 2);
                    leanh::lean_dec_ref_known(v___x_7225_, 1);
                    v___x_7227_ =
                        l_Lean_Meta_mkEqRefl(v_a_7226_, v_a_7210_, v_a_7211_, v_a_7212_, v_a_7213_);
                    if leanh::lean_obj_tag(v___x_7227_) == 0 {
                        v_a_7228_ = leanh::lean_ctor_get(v___x_7227_, 0);
                        leanh::lean_inc(v_a_7228_);
                        leanh::lean_dec_ref_known(v___x_7227_, 1);
                        leanh::lean_inc(v_a_7226_);
                        v___x_7229_ = l_Lean_Meta_mkEq(
                            v_e_7209_, v_a_7226_, v_a_7210_, v_a_7211_, v_a_7212_, v_a_7213_,
                        );
                        if leanh::lean_obj_tag(v___x_7229_) == 0 {
                            v_a_7230_ = leanh::lean_ctor_get(v___x_7229_, 0);
                            v_isSharedCheck_7243_ =
                                (!leanh::lean_is_exclusive(v___x_7229_)) as u8;
                            if v_isSharedCheck_7243_ == 0 {
                                v___x_7232_ = v___x_7229_;
                                v_isShared_7233_ = v_isSharedCheck_7243_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7230_);
                                leanh::lean_dec(v___x_7229_);
                                v___x_7232_ = leanh::lean_box(0);
                                v_isShared_7233_ = v_isSharedCheck_7243_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7228_);
                            leanh::lean_dec(v_a_7226_);
                            leanh::lean_del_object(v___x_7221_);
                            v_a_7244_ = leanh::lean_ctor_get(v___x_7229_, 0);
                            v_isSharedCheck_7251_ =
                                (!leanh::lean_is_exclusive(v___x_7229_)) as u8;
                            if v_isSharedCheck_7251_ == 0 {
                                v___x_7246_ = v___x_7229_;
                                v_isShared_7247_ = v_isSharedCheck_7251_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7244_);
                                leanh::lean_dec(v___x_7229_);
                                v___x_7246_ = leanh::lean_box(0);
                                v_isShared_7247_ = v_isSharedCheck_7251_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_7226_);
                        leanh::lean_del_object(v___x_7221_);
                        leanh::lean_dec_ref(v_e_7209_);
                        v_a_7252_ = leanh::lean_ctor_get(v___x_7227_, 0);
                        v_isSharedCheck_7259_ =
                            (!leanh::lean_is_exclusive(v___x_7227_)) as u8;
                        if v_isSharedCheck_7259_ == 0 {
                            v___x_7254_ = v___x_7227_;
                            v_isShared_7255_ = v_isSharedCheck_7259_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7252_);
                            leanh::lean_dec(v___x_7227_);
                            v___x_7254_ = leanh::lean_box(0);
                            v_isShared_7255_ = v_isSharedCheck_7259_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7221_);
                    leanh::lean_dec_ref(v_e_7209_);
                    v_a_7260_ = leanh::lean_ctor_get(v___x_7225_, 0);
                    v_isSharedCheck_7267_ = (!leanh::lean_is_exclusive(v___x_7225_)) as u8;
                    if v_isSharedCheck_7267_ == 0 {
                        v___x_7262_ = v___x_7225_;
                        v_isShared_7263_ = v_isSharedCheck_7267_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7260_);
                        leanh::lean_dec(v___x_7225_);
                        v___x_7262_ = leanh::lean_box(0);
                        v_isShared_7263_ = v_isSharedCheck_7267_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7234_ = 1;
                v___x_7235_ = l_Lean_Meta_mkExpectedPropHint(v_a_7228_, v_a_7230_);
                if v_isShared_7222_ == 0 {
                    leanh::lean_ctor_set(v___x_7221_, 0, v___x_7235_);
                    v___x_7237_ = v___x_7221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7242_, 0, v___x_7235_);
                    v___x_7237_ = v_reuseFailAlloc_7242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7238_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_7238_, 0, v_a_7226_);
                leanh::lean_ctor_set(v___x_7238_, 1, v___x_7237_);
                leanh::lean_ctor_set_uint8(
                    v___x_7238_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_7234_,
                );
                if v_isShared_7233_ == 0 {
                    leanh::lean_ctor_set(v___x_7232_, 0, v___x_7238_);
                    v___x_7240_ = v___x_7232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7241_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7241_, 0, v___x_7238_);
                    v___x_7240_ = v_reuseFailAlloc_7241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7240_;
            }
            5 => {
                if v_isShared_7247_ == 0 {
                    v___x_7249_ = v___x_7246_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7250_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 0, v_a_7244_);
                    v___x_7249_ = v_reuseFailAlloc_7250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7249_;
            }
            7 => {
                if v_isShared_7255_ == 0 {
                    v___x_7257_ = v___x_7254_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7258_, 0, v_a_7252_);
                    v___x_7257_ = v_reuseFailAlloc_7258_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7257_;
            }
            9 => {
                if v_isShared_7263_ == 0 {
                    v___x_7265_ = v___x_7262_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7266_, 0, v_a_7260_);
                    v___x_7265_ = v_reuseFailAlloc_7266_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7265_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___boxed(
    mut v_e_7270_: *mut leanh::LeanObject,
    mut v_a_7271_: *mut leanh::LeanObject,
    mut v_a_7272_: *mut leanh::LeanObject,
    mut v_a_7273_: *mut leanh::LeanObject,
    mut v_a_7274_: *mut leanh::LeanObject,
    mut v_a_7275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7276_ = l_Lean_Meta_Grind_replacePreMatchCond(
        v_e_7270_, v_a_7271_, v_a_7272_, v_a_7273_, v_a_7274_,
    );
    leanh::lean_dec(v_a_7274_);
    leanh::lean_dec_ref(v_a_7273_);
    leanh::lean_dec(v_a_7272_);
    leanh::lean_dec_ref(v_a_7271_);
    return v_res_7276_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(
    mut v_00_u03b1_7277_: *mut leanh::LeanObject,
    mut v_x_7278_: *mut leanh::LeanObject,
    mut v___y_7279_: *mut leanh::LeanObject,
    mut v___y_7280_: *mut leanh::LeanObject,
    mut v___y_7281_: *mut leanh::LeanObject,
    mut v___y_7282_: *mut leanh::LeanObject,
    mut v___y_7283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7285_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_7278_, v___y_7279_, v___y_7280_, v___y_7281_, v___y_7282_, v___y_7283_);
    return v___x_7285_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b1_7286_: *mut leanh::LeanObject,
    mut v_x_7287_: *mut leanh::LeanObject,
    mut v___y_7288_: *mut leanh::LeanObject,
    mut v___y_7289_: *mut leanh::LeanObject,
    mut v___y_7290_: *mut leanh::LeanObject,
    mut v___y_7291_: *mut leanh::LeanObject,
    mut v___y_7292_: *mut leanh::LeanObject,
    mut v___y_7293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7294_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_7286_, v_x_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_);
    leanh::lean_dec(v___y_7292_);
    leanh::lean_dec_ref(v___y_7291_);
    leanh::lean_dec(v___y_7290_);
    leanh::lean_dec_ref(v___y_7289_);
    leanh::lean_dec(v___y_7288_);
    return v_res_7294_;
}
pub unsafe fn l_Lean_Meta_Grind_isIte(mut v_e_7298_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: u8 = 0;
    v___x_7299_ = l_Lean_Meta_Grind_isIte___closed__1;
    v___x_7300_ = l_Lean_Expr_isAppOf(v_e_7298_, v___x_7299_);
    if v___x_7300_ == 0 {
        return v___x_7300_;
    } else {
        let mut v___x_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7303_: u8 = 0;
        v___x_7301_ = leanh::lean_unsigned_to_nat(5);
        v___x_7302_ = l_Lean_Expr_getAppNumArgs(v_e_7298_);
        v___x_7303_ = lean_nat_dec_le(v___x_7301_, v___x_7302_);
        leanh::lean_dec(v___x_7302_);
        return v___x_7303_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isIte___boxed(
    mut v_e_7304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7305_: u8 = 0;
    let mut v_r_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7305_ = l_Lean_Meta_Grind_isIte(v_e_7304_);
    leanh::lean_dec_ref(v_e_7304_);
    v_r_7306_ = leanh::lean_box((v_res_7305_) as usize);
    return v_r_7306_;
}
pub unsafe fn l_Lean_Meta_Grind_isDIte(mut v_e_7310_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: u8 = 0;
    v___x_7311_ = l_Lean_Meta_Grind_isDIte___closed__1;
    v___x_7312_ = l_Lean_Expr_isAppOf(v_e_7310_, v___x_7311_);
    if v___x_7312_ == 0 {
        return v___x_7312_;
    } else {
        let mut v___x_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7315_: u8 = 0;
        v___x_7313_ = leanh::lean_unsigned_to_nat(5);
        v___x_7314_ = l_Lean_Expr_getAppNumArgs(v_e_7310_);
        v___x_7315_ = lean_nat_dec_le(v___x_7313_, v___x_7314_);
        leanh::lean_dec(v___x_7314_);
        return v___x_7315_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isDIte___boxed(
    mut v_e_7316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7317_: u8 = 0;
    let mut v_r_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7317_ = l_Lean_Meta_Grind_isDIte(v_e_7316_);
    leanh::lean_dec_ref(v_e_7316_);
    v_r_7318_ = leanh::lean_box((v_res_7317_) as usize);
    return v_r_7318_;
}
pub unsafe fn l_Lean_Meta_Grind_getBinOp(
    mut v_e_7319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7320_: u8 = 0;
    v___x_7320_ = l_Lean_Expr_isApp(v_e_7319_);
    if v___x_7320_ == 0 {
        let mut v___x_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7321_ = leanh::lean_box(0);
        return v___x_7321_;
    } else {
        let mut v_f_7322_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7323_: u8 = 0;
        v_f_7322_ = l_Lean_Expr_appFn_x21(v_e_7319_);
        v___x_7323_ = l_Lean_Expr_isApp(v_f_7322_);
        if v___x_7323_ == 0 {
            let mut v___x_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_f_7322_);
            v___x_7324_ = leanh::lean_box(0);
            return v___x_7324_;
        } else {
            let mut v___x_7325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7326_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_7325_ = l_Lean_Expr_appFn_x21(v_f_7322_);
            leanh::lean_dec_ref(v_f_7322_);
            v___x_7326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_7326_, 0, v___x_7325_);
            return v___x_7326_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getBinOp___boxed(
    mut v_e_7327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7328_ = l_Lean_Meta_Grind_getBinOp(v_e_7327_);
    leanh::lean_dec_ref(v_e_7327_);
    return v_res_7328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Structure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Util(builtin);
}