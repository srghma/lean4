// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Util
// Imports: Lean.Meta.Tactic.Simp.Simproc Init.Simproc Lean.Meta.Tactic.Clear Lean.Meta.Sym.Util Init.Grind.Config Init.Grind.Util Lean.Structure
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Util::lean_grind_normalize;
use crate::lean_imports_rs::Lean::Util::FindExpr::lean_find_expr;
pub static l_Lean_MVarId_ensureNoMVar___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_ensureNoMVar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_ensureNoMVar___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_ensureNoMVar___closed__2_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_ensureNoMVar___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_ensureNoMVar___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_ensureNoMVar___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_ensureNoMVar___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_ensureNoMVar___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 118, 97, 114, 67, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 76, 67, 116, 120, 77, 86, 97, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2_value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 110, 32, 97, 115, 115, 111, 99, 105, 97, 116, 101, 100, 32, 102, 117, 108, 108, 32, 110, 97, 109, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_unfoldReducible___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Sym_unfoldReducible___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_unfoldReducible___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_unfoldReducible___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_betaReduce___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_betaReduce___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_betaReduce___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_betaReduce___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            907667957179513571 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10854111772627758120 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__4_value)
                as *mut crate::leanh::LeanObject,
            3628558105408452239 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_byContra_x3f___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_byContra_x3f___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_byContra_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_byContra_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_byContra_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11419739819762551189 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_byContra_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_byContra_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [116, 104, 101, 32, 103, 111, 97, 108, 32, 109, 101, 110, 116, 105, 111, 110, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<94> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [96, 44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 98, 101, 105, 110, 103, 32, 100, 101, 102, 105, 110, 101, 100, 46, 32, 84, 111, 32, 97, 118, 111, 105, 100, 32, 99, 105, 114, 99, 117, 108, 97, 114, 32, 114, 101, 97, 115, 111, 110, 105, 110, 103, 44, 32, 116, 114, 121, 32, 114, 101, 119, 114, 105, 116, 105, 110, 103, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 116, 111, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [96, 32, 98, 101, 102, 111, 114, 101, 32, 117, 115, 105, 110, 103, 32, 96, 103, 114, 105, 110, 100, 96, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_clearImplDetails___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_MVarId_clearImplDetails___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_clearImplDetails___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_ensureNoMVar___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_clearImplDetails___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12811869134523501583 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_clearImplDetails___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearImplDetails___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0_value:
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
    m_fun: l_Lean_Expr_isMData___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__2_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13563742693681136756 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_markAsMatchCond___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16774854854508800365 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_markAsMatchCond___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2148952242689989847 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_markAsPreMatchCond___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [114, 101, 100, 117, 99, 101, 80, 114, 101, 77, 97, 116, 99, 104, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__0_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_markAsMatchCond___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__1_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,8386783702137954454 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1_value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value: crate::leanh::LeanArrayObject<2> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__3_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_replacePreMatchCond___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_isPreMatchCond___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_replacePreMatchCond___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_replacePreMatchCond___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_replacePreMatchCond___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_replacePreMatchCond___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_replacePreMatchCond___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_replacePreMatchCond___closed__2_value:
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
    m_fun: l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_replacePreMatchCond___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_replacePreMatchCond___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isIte___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_isIte___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isIte___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isIte___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isIte___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18356704233129443855 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isIte___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isIte___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isDIte___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_isDIte___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isDIte___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_isDIte___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_isDIte___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8391571994004792969 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_isDIte___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_isDIte___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
    mut v_e_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3688_: u8 = 0;
    let mut v_unused_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3668_ = l_Lean_Expr_hasMVar(v_e_3665_);
                if v___x_3668_ == 0 {
                    v___x_3669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3669_, 0, v_e_3665_);
                    return v___x_3669_;
                } else {
                    v___x_3670_ = lean_st_ref_get(v___y_3666_);
                    v_mctx_3671_ = crate::leanh::lean_ctor_get(v___x_3670_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3671_);
                    crate::leanh::lean_dec(v___x_3670_);
                    v___x_3672_ = l_Lean_instantiateMVarsCore(v_mctx_3671_, v_e_3665_);
                    v_fst_3673_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    crate::leanh::lean_inc(v_fst_3673_);
                    v_snd_3674_ = crate::leanh::lean_ctor_get(v___x_3672_, 1);
                    crate::leanh::lean_inc(v_snd_3674_);
                    crate::leanh::lean_dec_ref(v___x_3672_);
                    v___x_3675_ = lean_st_ref_take(v___y_3666_);
                    v_cache_3676_ = crate::leanh::lean_ctor_get(v___x_3675_, 1);
                    v_zetaDeltaFVarIds_3677_ = crate::leanh::lean_ctor_get(v___x_3675_, 2);
                    v_postponed_3678_ = crate::leanh::lean_ctor_get(v___x_3675_, 3);
                    v_diag_3679_ = crate::leanh::lean_ctor_get(v___x_3675_, 4);
                    v_isSharedCheck_3688_ = (!crate::leanh::lean_is_exclusive(v___x_3675_)) as u8;
                    if v_isSharedCheck_3688_ == 0 {
                        v_unused_3689_ = crate::leanh::lean_ctor_get(v___x_3675_, 0);
                        crate::leanh::lean_dec(v_unused_3689_);
                        v___x_3681_ = v___x_3675_;
                        v_isShared_3682_ = v_isSharedCheck_3688_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3679_);
                        crate::leanh::lean_inc(v_postponed_3678_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3677_);
                        crate::leanh::lean_inc(v_cache_3676_);
                        crate::leanh::lean_dec(v___x_3675_);
                        v___x_3681_ = crate::leanh::lean_box(0);
                        v_isShared_3682_ = v_isSharedCheck_3688_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3681_, 0, v_snd_3674_);
                    v___x_3684_ = v___x_3681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_snd_3674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_cache_3676_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3687_,
                        2,
                        v_zetaDeltaFVarIds_3677_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_postponed_3678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_diag_3679_);
                    v___x_3684_ = v_reuseFailAlloc_3687_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3685_ = lean_st_ref_set(v___y_3666_, v___x_3684_);
                v___x_3686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3686_, 0, v_fst_3673_);
                return v___x_3686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg___boxed(
    mut v_e_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
        v_e_3690_,
        v___y_3691_,
    );
    crate::leanh::lean_dec(v___y_3691_);
    return v_res_3693_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(
    mut v_e_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
    mut v___y_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
        v_e_3694_,
        v___y_3696_,
    );
    return v___x_3700_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___boxed(
    mut v_e_3701_: *mut crate::leanh::LeanObject,
    mut v___y_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3707_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0(
        v_e_3701_,
        v___y_3702_,
        v___y_3703_,
        v___y_3704_,
        v___y_3705_,
    );
    crate::leanh::lean_dec(v___y_3705_);
    crate::leanh::lean_dec_ref(v___y_3704_);
    crate::leanh::lean_dec(v___y_3703_);
    crate::leanh::lean_dec_ref(v___y_3702_);
    return v_res_3707_;
}
pub unsafe fn _init_l_Lean_MVarId_ensureNoMVar___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l_Lean_MVarId_ensureNoMVar___closed__3;
    v___x_3715_ = l_Lean_MessageData_ofFormat(v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn _init_l_Lean_MVarId_ensureNoMVar___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_ensureNoMVar___closed__4),
        core::ptr::addr_of_mut!(l_Lean_MVarId_ensureNoMVar___closed__4_once),
        _init_l_Lean_MVarId_ensureNoMVar___closed__4,
    );
    v___x_3717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3717_, 0, v___x_3716_);
    return v___x_3717_;
}
pub unsafe fn l_Lean_MVarId_ensureNoMVar(
    mut v_mvarId_3718_: *mut crate::leanh::LeanObject,
    mut v_a_3719_: *mut crate::leanh::LeanObject,
    mut v_a_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut v_a_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3718_);
                v___x_3724_ = l_Lean_MVarId_getType(
                    v_mvarId_3718_,
                    v_a_3719_,
                    v_a_3720_,
                    v_a_3721_,
                    v_a_3722_,
                );
                if crate::leanh::lean_obj_tag(v___x_3724_) == 0 {
                    v_a_3725_ = crate::leanh::lean_ctor_get(v___x_3724_, 0);
                    crate::leanh::lean_inc(v_a_3725_);
                    crate::leanh::lean_dec_ref_known(v___x_3724_, 1);
                    v___x_3726_ =
                        l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(
                            v_a_3725_, v_a_3720_,
                        );
                    v_a_3727_ = crate::leanh::lean_ctor_get(v___x_3726_, 0);
                    v_isSharedCheck_3739_ = (!crate::leanh::lean_is_exclusive(v___x_3726_)) as u8;
                    if v_isSharedCheck_3739_ == 0 {
                        v___x_3729_ = v___x_3726_;
                        v_isShared_3730_ = v_isSharedCheck_3739_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3727_);
                        crate::leanh::lean_dec(v___x_3726_);
                        v___x_3729_ = crate::leanh::lean_box(0);
                        v_isShared_3730_ = v_isSharedCheck_3739_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3718_);
                    v_a_3740_ = crate::leanh::lean_ctor_get(v___x_3724_, 0);
                    v_isSharedCheck_3747_ = (!crate::leanh::lean_is_exclusive(v___x_3724_)) as u8;
                    if v_isSharedCheck_3747_ == 0 {
                        v___x_3742_ = v___x_3724_;
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3740_);
                        crate::leanh::lean_dec(v___x_3724_);
                        v___x_3742_ = crate::leanh::lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3747_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3731_ = l_Lean_Expr_hasExprMVar(v_a_3727_);
                crate::leanh::lean_dec(v_a_3727_);
                if v___x_3731_ == 0 {
                    crate::leanh::lean_dec(v_mvarId_3718_);
                    v___x_3732_ = crate::leanh::lean_box(0);
                    if v_isShared_3730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3729_, 0, v___x_3732_);
                        v___x_3734_ = v___x_3729_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
                        v___x_3734_ = v_reuseFailAlloc_3735_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3729_);
                    v___x_3736_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                    v___x_3737_ = crate::leanh::lean_obj_once(
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
                    v_reuseFailAlloc_3746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
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
    mut v_mvarId_3748_: *mut crate::leanh::LeanObject,
    mut v_a_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: *mut crate::leanh::LeanObject,
    mut v_a_3751_: *mut crate::leanh::LeanObject,
    mut v_a_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ =
        l_Lean_MVarId_ensureNoMVar(v_mvarId_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
    crate::leanh::lean_dec(v_a_3752_);
    crate::leanh::lean_dec_ref(v_a_3751_);
    crate::leanh::lean_dec(v_a_3750_);
    crate::leanh::lean_dec_ref(v_a_3749_);
    return v_res_3754_;
}
pub unsafe fn _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3755_;
}
pub unsafe fn l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(
    mut v_msg_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v_toFunctor_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___f_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v_toFunctor_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___f_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361__overap_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut v_unused_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut v_unused_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3829_: u8 = 0;
    let mut v_unused_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__0);
                v___x_3767_ = l_StateRefT_x27_instMonad___redArg(v___x_3766_);
                v_toApplicative_3768_ = crate::leanh::lean_ctor_get(v___x_3767_, 0);
                v_isSharedCheck_3829_ = (!crate::leanh::lean_is_exclusive(v___x_3767_)) as u8;
                if v_isSharedCheck_3829_ == 0 {
                    v_unused_3830_ = crate::leanh::lean_ctor_get(v___x_3767_, 1);
                    crate::leanh::lean_dec(v_unused_3830_);
                    v___x_3770_ = v___x_3767_;
                    v_isShared_3771_ = v_isSharedCheck_3829_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3768_);
                    crate::leanh::lean_dec(v___x_3767_);
                    v___x_3770_ = crate::leanh::lean_box(0);
                    v_isShared_3771_ = v_isSharedCheck_3829_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3772_ = crate::leanh::lean_ctor_get(v_toApplicative_3768_, 0);
                v_toSeq_3773_ = crate::leanh::lean_ctor_get(v_toApplicative_3768_, 2);
                v_toSeqLeft_3774_ = crate::leanh::lean_ctor_get(v_toApplicative_3768_, 3);
                v_toSeqRight_3775_ = crate::leanh::lean_ctor_get(v_toApplicative_3768_, 4);
                v_isSharedCheck_3827_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3768_)) as u8;
                if v_isSharedCheck_3827_ == 0 {
                    v_unused_3828_ = crate::leanh::lean_ctor_get(v_toApplicative_3768_, 1);
                    crate::leanh::lean_dec(v_unused_3828_);
                    v___x_3777_ = v_toApplicative_3768_;
                    v_isShared_3778_ = v_isSharedCheck_3827_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3775_);
                    crate::leanh::lean_inc(v_toSeqLeft_3774_);
                    crate::leanh::lean_inc(v_toSeq_3773_);
                    crate::leanh::lean_inc(v_toFunctor_3772_);
                    crate::leanh::lean_dec(v_toApplicative_3768_);
                    v___x_3777_ = crate::leanh::lean_box(0);
                    v_isShared_3778_ = v_isSharedCheck_3827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3779_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__1;
                v___f_3780_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3772_);
                v___f_3781_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3781_, 0, v_toFunctor_3772_);
                v___f_3782_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3782_, 0, v_toFunctor_3772_);
                v___x_3783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3783_, 0, v___f_3781_);
                crate::leanh::lean_ctor_set(v___x_3783_, 1, v___f_3782_);
                v___f_3784_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3784_, 0, v_toSeqRight_3775_);
                v___f_3785_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3785_, 0, v_toSeqLeft_3774_);
                v___f_3786_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3786_, 0, v_toSeq_3773_);
                if v_isShared_3778_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3777_, 4, v___f_3784_);
                    crate::leanh::lean_ctor_set(v___x_3777_, 3, v___f_3785_);
                    crate::leanh::lean_ctor_set(v___x_3777_, 2, v___f_3786_);
                    crate::leanh::lean_ctor_set(v___x_3777_, 1, v___f_3779_);
                    crate::leanh::lean_ctor_set(v___x_3777_, 0, v___x_3783_);
                    v___x_3788_ = v___x_3777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___f_3779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 2, v___f_3786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 3, v___f_3785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 4, v___f_3784_);
                    v___x_3788_ = v_reuseFailAlloc_3826_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3771_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3770_, 1, v___f_3780_);
                    crate::leanh::lean_ctor_set(v___x_3770_, 0, v___x_3788_);
                    v___x_3790_ = v___x_3770_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___f_3780_);
                    v___x_3790_ = v_reuseFailAlloc_3825_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3791_ = l_StateRefT_x27_instMonad___redArg(v___x_3790_);
                v_toApplicative_3792_ = crate::leanh::lean_ctor_get(v___x_3791_, 0);
                v_isSharedCheck_3823_ = (!crate::leanh::lean_is_exclusive(v___x_3791_)) as u8;
                if v_isSharedCheck_3823_ == 0 {
                    v_unused_3824_ = crate::leanh::lean_ctor_get(v___x_3791_, 1);
                    crate::leanh::lean_dec(v_unused_3824_);
                    v___x_3794_ = v___x_3791_;
                    v_isShared_3795_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3792_);
                    crate::leanh::lean_dec(v___x_3791_);
                    v___x_3794_ = crate::leanh::lean_box(0);
                    v_isShared_3795_ = v_isSharedCheck_3823_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3796_ = crate::leanh::lean_ctor_get(v_toApplicative_3792_, 0);
                v_toSeq_3797_ = crate::leanh::lean_ctor_get(v_toApplicative_3792_, 2);
                v_toSeqLeft_3798_ = crate::leanh::lean_ctor_get(v_toApplicative_3792_, 3);
                v_toSeqRight_3799_ = crate::leanh::lean_ctor_get(v_toApplicative_3792_, 4);
                v_isSharedCheck_3821_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3792_)) as u8;
                if v_isSharedCheck_3821_ == 0 {
                    v_unused_3822_ = crate::leanh::lean_ctor_get(v_toApplicative_3792_, 1);
                    crate::leanh::lean_dec(v_unused_3822_);
                    v___x_3801_ = v_toApplicative_3792_;
                    v_isShared_3802_ = v_isSharedCheck_3821_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3799_);
                    crate::leanh::lean_inc(v_toSeqLeft_3798_);
                    crate::leanh::lean_inc(v_toSeq_3797_);
                    crate::leanh::lean_inc(v_toFunctor_3796_);
                    crate::leanh::lean_dec(v_toApplicative_3792_);
                    v___x_3801_ = crate::leanh::lean_box(0);
                    v_isShared_3802_ = v_isSharedCheck_3821_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3803_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__3;
                v___f_3804_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_3796_);
                v___f_3805_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3805_, 0, v_toFunctor_3796_);
                v___f_3806_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3806_, 0, v_toFunctor_3796_);
                v___x_3807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3807_, 0, v___f_3805_);
                crate::leanh::lean_ctor_set(v___x_3807_, 1, v___f_3806_);
                v___f_3808_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3808_, 0, v_toSeqRight_3799_);
                v___f_3809_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3809_, 0, v_toSeqLeft_3798_);
                v___f_3810_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3810_, 0, v_toSeq_3797_);
                if v_isShared_3802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3801_, 4, v___f_3808_);
                    crate::leanh::lean_ctor_set(v___x_3801_, 3, v___f_3809_);
                    crate::leanh::lean_ctor_set(v___x_3801_, 2, v___f_3810_);
                    crate::leanh::lean_ctor_set(v___x_3801_, 1, v___f_3803_);
                    crate::leanh::lean_ctor_set(v___x_3801_, 0, v___x_3807_);
                    v___x_3812_ = v___x_3801_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 1, v___f_3803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 2, v___f_3810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 3, v___f_3809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 4, v___f_3808_);
                    v___x_3812_ = v_reuseFailAlloc_3820_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3794_, 1, v___f_3804_);
                    crate::leanh::lean_ctor_set(v___x_3794_, 0, v___x_3812_);
                    v___x_3814_ = v___x_3794_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___f_3804_);
                    v___x_3814_ = v_reuseFailAlloc_3819_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3815_ = l_Lean_instInhabitedLocalContext_default;
                v___x_3816_ = l_instInhabitedOfMonad___redArg(v___x_3814_, v___x_3815_);
                v___x_1361__overap_3817_ = lean_panic_fn_borrowed(v___x_3816_, v_msg_3760_);
                crate::leanh::lean_dec(v___x_3816_);
                crate::leanh::lean_inc(v___y_3764_);
                crate::leanh::lean_inc_ref(v___y_3763_);
                crate::leanh::lean_inc(v___y_3762_);
                crate::leanh::lean_inc_ref(v___y_3761_);
                v___x_3818_ = crate::leanh::lean_apply_5(
                    v___x_1361__overap_3817_,
                    v___y_3761_,
                    v___y_3762_,
                    v___y_3763_,
                    v___y_3764_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1___boxed(
    mut v_msg_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3837_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v_msg_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
    crate::leanh::lean_dec(v___y_3835_);
    crate::leanh::lean_dec_ref(v___y_3834_);
    crate::leanh::lean_dec(v___y_3833_);
    crate::leanh::lean_dec_ref(v___y_3832_);
    return v_res_3837_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(
    mut v_t_3838_: *mut crate::leanh::LeanObject,
    mut v_k_3839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: u8 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3838_) == 0 {
                    v_k_3840_ = crate::leanh::lean_ctor_get(v_t_3838_, 1);
                    v_v_3841_ = crate::leanh::lean_ctor_get(v_t_3838_, 2);
                    v_l_3842_ = crate::leanh::lean_ctor_get(v_t_3838_, 3);
                    v_r_3843_ = crate::leanh::lean_ctor_get(v_t_3838_, 4);
                    v___x_3844_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3839_, v_k_3840_);
                    match v___x_3844_ {
                        0 => {
                            v_t_3838_ = v_l_3842_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_3841_);
                            v___x_3846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3846_, 0, v_v_3841_);
                            return v___x_3846_;
                        }
                        _ => {
                            v_t_3838_ = v_r_3843_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_3848_ = crate::leanh::lean_box(0);
                    return v___x_3848_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg___boxed(
    mut v_t_3849_: *mut crate::leanh::LeanObject,
    mut v_k_3850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3851_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_3849_, v_k_3850_);
    crate::leanh::lean_dec(v_k_3850_);
    crate::leanh::lean_dec(v_t_3849_);
    return v_res_3851_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(
    mut v_auxDeclToFullName_3856_: *mut crate::leanh::LeanObject,
    mut v_as_3857_: *mut crate::leanh::LeanObject,
    mut v_i_3858_: usize,
    mut v_stop_3859_: usize,
    mut v_b_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: usize = 0;
    let mut v___x_3869_: usize = 0;
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3874_: u8 = 0;
    let mut v_fvarId_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_fvarId_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bi_3907_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_fvarId_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_3923_: u8 = 0;
    let mut v_kind_3924_: u8 = 0;
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut v_a_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3941_: u8 = 0;
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3871_ = lean_usize_dec_eq(v_i_3858_, v_stop_3859_);
                if v___x_3871_ == 0 {
                    v___x_3872_ = lean_array_uget_borrowed(v_as_3857_, v_i_3858_);
                    if crate::leanh::lean_obj_tag(v___x_3872_) == 0 {
                        v_a_3867_ = v_b_3860_;
                        state = 1;
                        continue;
                    } else {
                        v_val_3873_ = crate::leanh::lean_ctor_get(v___x_3872_, 0);
                        if crate::leanh::lean_obj_tag(v_val_3873_) == 0 {
                            v_kind_3874_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_3873_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1)
                                    as u32,
                            );
                            if v_kind_3874_ == 2 {
                                v_fvarId_3875_ = crate::leanh::lean_ctor_get(v_val_3873_, 1);
                                v_userName_3876_ = crate::leanh::lean_ctor_get(v_val_3873_, 2);
                                v_type_3877_ = crate::leanh::lean_ctor_get(v_val_3873_, 3);
                                crate::leanh::lean_inc_ref(v_type_3877_);
                                v___x_3878_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_3877_, v___y_3862_);
                                if crate::leanh::lean_obj_tag(v___x_3878_) == 0 {
                                    v_a_3879_ = crate::leanh::lean_ctor_get(v___x_3878_, 0);
                                    crate::leanh::lean_inc(v_a_3879_);
                                    crate::leanh::lean_dec_ref_known(v___x_3878_, 1);
                                    v___x_3880_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_auxDeclToFullName_3856_, v_fvarId_3875_);
                                    if crate::leanh::lean_obj_tag(v___x_3880_) == 1 {
                                        v_val_3881_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                                        crate::leanh::lean_inc(v_val_3881_);
                                        crate::leanh::lean_dec_ref_known(v___x_3880_, 1);
                                        crate::leanh::lean_inc(v_userName_3876_);
                                        crate::leanh::lean_inc(v_fvarId_3875_);
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
                                        crate::leanh::lean_dec(v___x_3880_);
                                        crate::leanh::lean_dec(v_a_3879_);
                                        crate::leanh::lean_dec_ref(v_b_3860_);
                                        v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__0;
                                        v___x_3884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__1;
                                        v___x_3885_ = crate::leanh::lean_unsigned_to_nat(635);
                                        v___x_3886_ = crate::leanh::lean_unsigned_to_nat(12);
                                        v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__2;
                                        v___x_3888_ = 1;
                                        crate::leanh::lean_inc(v_userName_3876_);
                                        v___x_3889_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_3876_, v___x_3888_);
                                        v___x_3890_ = lean_string_append(v___x_3887_, v___x_3889_);
                                        crate::leanh::lean_dec_ref(v___x_3889_);
                                        v___x_3891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6___closed__3;
                                        v___x_3892_ = lean_string_append(v___x_3890_, v___x_3891_);
                                        v___x_3893_ = l_mkPanicMessageWithDecl(
                                            v___x_3883_,
                                            v___x_3884_,
                                            v___x_3885_,
                                            v___x_3886_,
                                            v___x_3892_,
                                        );
                                        crate::leanh::lean_dec_ref(v___x_3892_);
                                        v___x_3894_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__1(v___x_3893_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
                                        if crate::leanh::lean_obj_tag(v___x_3894_) == 0 {
                                            v_a_3895_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
                                            crate::leanh::lean_inc(v_a_3895_);
                                            crate::leanh::lean_dec_ref_known(v___x_3894_, 1);
                                            v_a_3867_ = v_a_3895_;
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_3894_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_b_3860_);
                                    v_a_3896_ = crate::leanh::lean_ctor_get(v___x_3878_, 0);
                                    v_isSharedCheck_3903_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3878_)) as u8;
                                    if v_isSharedCheck_3903_ == 0 {
                                        v___x_3898_ = v___x_3878_;
                                        v_isShared_3899_ = v_isSharedCheck_3903_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3896_);
                                        crate::leanh::lean_dec(v___x_3878_);
                                        v___x_3898_ = crate::leanh::lean_box(0);
                                        v_isShared_3899_ = v_isSharedCheck_3903_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                v_fvarId_3904_ = crate::leanh::lean_ctor_get(v_val_3873_, 1);
                                v_userName_3905_ = crate::leanh::lean_ctor_get(v_val_3873_, 2);
                                v_type_3906_ = crate::leanh::lean_ctor_get(v_val_3873_, 3);
                                v_bi_3907_ = crate::leanh::lean_ctor_get_uint8(
                                    v_val_3873_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                );
                                crate::leanh::lean_inc_ref(v_type_3906_);
                                v___x_3908_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_3906_, v___y_3862_);
                                if crate::leanh::lean_obj_tag(v___x_3908_) == 0 {
                                    v_a_3909_ = crate::leanh::lean_ctor_get(v___x_3908_, 0);
                                    crate::leanh::lean_inc(v_a_3909_);
                                    crate::leanh::lean_dec_ref_known(v___x_3908_, 1);
                                    crate::leanh::lean_inc(v_userName_3905_);
                                    crate::leanh::lean_inc(v_fvarId_3904_);
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
                                    crate::leanh::lean_dec_ref(v_b_3860_);
                                    v_a_3911_ = crate::leanh::lean_ctor_get(v___x_3908_, 0);
                                    v_isSharedCheck_3918_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3908_)) as u8;
                                    if v_isSharedCheck_3918_ == 0 {
                                        v___x_3913_ = v___x_3908_;
                                        v_isShared_3914_ = v_isSharedCheck_3918_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3911_);
                                        crate::leanh::lean_dec(v___x_3908_);
                                        v___x_3913_ = crate::leanh::lean_box(0);
                                        v_isShared_3914_ = v_isSharedCheck_3918_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_fvarId_3919_ = crate::leanh::lean_ctor_get(v_val_3873_, 1);
                            v_userName_3920_ = crate::leanh::lean_ctor_get(v_val_3873_, 2);
                            v_type_3921_ = crate::leanh::lean_ctor_get(v_val_3873_, 3);
                            v_value_3922_ = crate::leanh::lean_ctor_get(v_val_3873_, 4);
                            v_nondep_3923_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_3873_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                            );
                            v_kind_3924_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_3873_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_type_3921_);
                            v___x_3925_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_3921_, v___y_3862_);
                            if crate::leanh::lean_obj_tag(v___x_3925_) == 0 {
                                v_a_3926_ = crate::leanh::lean_ctor_get(v___x_3925_, 0);
                                crate::leanh::lean_inc(v_a_3926_);
                                crate::leanh::lean_dec_ref_known(v___x_3925_, 1);
                                crate::leanh::lean_inc_ref(v_value_3922_);
                                v___x_3927_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_value_3922_, v___y_3862_);
                                if crate::leanh::lean_obj_tag(v___x_3927_) == 0 {
                                    v_a_3928_ = crate::leanh::lean_ctor_get(v___x_3927_, 0);
                                    crate::leanh::lean_inc(v_a_3928_);
                                    crate::leanh::lean_dec_ref_known(v___x_3927_, 1);
                                    crate::leanh::lean_inc(v_userName_3920_);
                                    crate::leanh::lean_inc(v_fvarId_3919_);
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
                                    crate::leanh::lean_dec(v_a_3926_);
                                    crate::leanh::lean_dec_ref(v_b_3860_);
                                    v_a_3930_ = crate::leanh::lean_ctor_get(v___x_3927_, 0);
                                    v_isSharedCheck_3937_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3927_)) as u8;
                                    if v_isSharedCheck_3937_ == 0 {
                                        v___x_3932_ = v___x_3927_;
                                        v_isShared_3933_ = v_isSharedCheck_3937_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3930_);
                                        crate::leanh::lean_dec(v___x_3927_);
                                        v___x_3932_ = crate::leanh::lean_box(0);
                                        v_isShared_3933_ = v_isSharedCheck_3937_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_b_3860_);
                                v_a_3938_ = crate::leanh::lean_ctor_get(v___x_3925_, 0);
                                v_isSharedCheck_3945_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3925_)) as u8;
                                if v_isSharedCheck_3945_ == 0 {
                                    v___x_3940_ = v___x_3925_;
                                    v_isShared_3941_ = v_isSharedCheck_3945_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3938_);
                                    crate::leanh::lean_dec(v___x_3925_);
                                    v___x_3940_ = crate::leanh::lean_box(0);
                                    v_isShared_3941_ = v_isSharedCheck_3945_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_3946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3946_, 0, v_b_3860_);
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
                    v_reuseFailAlloc_3902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
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
                    v_reuseFailAlloc_3917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
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
                    v_reuseFailAlloc_3936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
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
                    v_reuseFailAlloc_3944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
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
    mut v_auxDeclToFullName_3947_: *mut crate::leanh::LeanObject,
    mut v_as_3948_: *mut crate::leanh::LeanObject,
    mut v_i_3949_: *mut crate::leanh::LeanObject,
    mut v_stop_3950_: *mut crate::leanh::LeanObject,
    mut v_b_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3957_: usize = 0;
    let mut v_stop_boxed_3958_: usize = 0;
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3957_ = crate::leanh::lean_unbox_usize(v_i_3949_);
    crate::leanh::lean_dec(v_i_3949_);
    v_stop_boxed_3958_ = crate::leanh::lean_unbox_usize(v_stop_3950_);
    crate::leanh::lean_dec(v_stop_3950_);
    v_res_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_3947_, v_as_3948_, v_i_boxed_3957_, v_stop_boxed_3958_, v_b_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    crate::leanh::lean_dec_ref(v_as_3948_);
    crate::leanh::lean_dec(v_auxDeclToFullName_3947_);
    return v_res_3959_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(
    mut v_auxDeclToFullName_3960_: *mut crate::leanh::LeanObject,
    mut v_x_3961_: *mut crate::leanh::LeanObject,
    mut v_x_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: u8 = 0;
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: usize = 0;
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut v_vs_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: usize = 0;
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: usize = 0;
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3961_) == 0 {
                    v_cs_3968_ = crate::leanh::lean_ctor_get(v_x_3961_, 0);
                    v_isSharedCheck_3988_ = (!crate::leanh::lean_is_exclusive(v_x_3961_)) as u8;
                    if v_isSharedCheck_3988_ == 0 {
                        v___x_3970_ = v_x_3961_;
                        v_isShared_3971_ = v_isSharedCheck_3988_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_3968_);
                        crate::leanh::lean_dec(v_x_3961_);
                        v___x_3970_ = crate::leanh::lean_box(0);
                        v_isShared_3971_ = v_isSharedCheck_3988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_3989_ = crate::leanh::lean_ctor_get(v_x_3961_, 0);
                    v_isSharedCheck_4009_ = (!crate::leanh::lean_is_exclusive(v_x_3961_)) as u8;
                    if v_isSharedCheck_4009_ == 0 {
                        v___x_3991_ = v_x_3961_;
                        v_isShared_3992_ = v_isSharedCheck_4009_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3989_);
                        crate::leanh::lean_dec(v_x_3961_);
                        v___x_3991_ = crate::leanh::lean_box(0);
                        v_isShared_3992_ = v_isSharedCheck_4009_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3972_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3973_ = lean_array_get_size(v_cs_3968_);
                v___x_3974_ = lean_nat_dec_lt(v___x_3972_, v___x_3973_);
                if v___x_3974_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_3968_);
                    if v_isShared_3971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3970_, 0, v_x_3962_);
                        v___x_3976_ = v___x_3970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_x_3962_);
                        v___x_3976_ = v_reuseFailAlloc_3977_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3978_ = lean_nat_dec_le(v___x_3973_, v___x_3973_);
                    if v___x_3978_ == 0 {
                        if v___x_3974_ == 0 {
                            crate::leanh::lean_dec_ref(v_cs_3968_);
                            if v_isShared_3971_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3970_, 0, v_x_3962_);
                                v___x_3980_ = v___x_3970_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3981_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_x_3962_);
                                v___x_3980_ = v_reuseFailAlloc_3981_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3970_);
                            v___x_3982_ = 0usize;
                            v___x_3983_ = lean_usize_of_nat(v___x_3973_);
                            v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_3960_, v_cs_3968_, v___x_3982_, v___x_3983_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                            crate::leanh::lean_dec_ref(v_cs_3968_);
                            return v___x_3984_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3970_);
                        v___x_3985_ = 0usize;
                        v___x_3986_ = lean_usize_of_nat(v___x_3973_);
                        v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_3960_, v_cs_3968_, v___x_3985_, v___x_3986_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                        crate::leanh::lean_dec_ref(v_cs_3968_);
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
                v___x_3993_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3994_ = lean_array_get_size(v_vs_3989_);
                v___x_3995_ = lean_nat_dec_lt(v___x_3993_, v___x_3994_);
                if v___x_3995_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_3989_);
                    if v_isShared_3992_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3991_, 0);
                        crate::leanh::lean_ctor_set(v___x_3991_, 0, v_x_3962_);
                        v___x_3997_ = v___x_3991_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3998_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_x_3962_);
                        v___x_3997_ = v_reuseFailAlloc_3998_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_3999_ = lean_nat_dec_le(v___x_3994_, v___x_3994_);
                    if v___x_3999_ == 0 {
                        if v___x_3995_ == 0 {
                            crate::leanh::lean_dec_ref(v_vs_3989_);
                            if v_isShared_3992_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_3991_, 0);
                                crate::leanh::lean_ctor_set(v___x_3991_, 0, v_x_3962_);
                                v___x_4001_ = v___x_3991_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_4002_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_x_3962_);
                                v___x_4001_ = v_reuseFailAlloc_4002_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3991_);
                            v___x_4003_ = 0usize;
                            v___x_4004_ = lean_usize_of_nat(v___x_3994_);
                            v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_3960_, v_vs_3989_, v___x_4003_, v___x_4004_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                            crate::leanh::lean_dec_ref(v_vs_3989_);
                            return v___x_4005_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3991_);
                        v___x_4006_ = 0usize;
                        v___x_4007_ = lean_usize_of_nat(v___x_3994_);
                        v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_3960_, v_vs_3989_, v___x_4006_, v___x_4007_, v_x_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
                        crate::leanh::lean_dec_ref(v_vs_3989_);
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
    mut v_auxDeclToFullName_4010_: *mut crate::leanh::LeanObject,
    mut v_as_4011_: *mut crate::leanh::LeanObject,
    mut v_i_4012_: usize,
    mut v_stop_4013_: usize,
    mut v_b_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: usize = 0;
    let mut v___x_4025_: usize = 0;
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4020_ = lean_usize_dec_eq(v_i_4012_, v_stop_4013_);
                if v___x_4020_ == 0 {
                    v___x_4021_ = lean_array_uget_borrowed(v_as_4011_, v_i_4012_);
                    crate::leanh::lean_inc(v___x_4021_);
                    v___x_4022_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_4010_, v___x_4021_, v_b_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
                    if crate::leanh::lean_obj_tag(v___x_4022_) == 0 {
                        v_a_4023_ = crate::leanh::lean_ctor_get(v___x_4022_, 0);
                        crate::leanh::lean_inc(v_a_4023_);
                        crate::leanh::lean_dec_ref_known(v___x_4022_, 1);
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
                    v___x_4027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4027_, 0, v_b_4014_);
                    return v___x_4027_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(
    mut v_auxDeclToFullName_4028_: *mut crate::leanh::LeanObject,
    mut v_as_4029_: *mut crate::leanh::LeanObject,
    mut v_i_4030_: *mut crate::leanh::LeanObject,
    mut v_stop_4031_: *mut crate::leanh::LeanObject,
    mut v_b_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4038_: usize = 0;
    let mut v_stop_boxed_4039_: usize = 0;
    let mut v_res_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4038_ = crate::leanh::lean_unbox_usize(v_i_4030_);
    crate::leanh::lean_dec(v_i_4030_);
    v_stop_boxed_4039_ = crate::leanh::lean_unbox_usize(v_stop_4031_);
    crate::leanh::lean_dec(v_stop_4031_);
    v_res_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_4028_, v_as_4029_, v_i_boxed_4038_, v_stop_boxed_4039_, v_b_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
    crate::leanh::lean_dec(v___y_4036_);
    crate::leanh::lean_dec_ref(v___y_4035_);
    crate::leanh::lean_dec(v___y_4034_);
    crate::leanh::lean_dec_ref(v___y_4033_);
    crate::leanh::lean_dec_ref(v_as_4029_);
    crate::leanh::lean_dec(v_auxDeclToFullName_4028_);
    return v_res_4040_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7___boxed(
    mut v_auxDeclToFullName_4041_: *mut crate::leanh::LeanObject,
    mut v_x_4042_: *mut crate::leanh::LeanObject,
    mut v_x_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_4041_, v_x_4042_, v_x_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
    crate::leanh::lean_dec(v___y_4047_);
    crate::leanh::lean_dec_ref(v___y_4046_);
    crate::leanh::lean_dec(v___y_4045_);
    crate::leanh::lean_dec_ref(v___y_4044_);
    crate::leanh::lean_dec(v_auxDeclToFullName_4041_);
    return v_res_4049_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_4050_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(
    mut v_auxDeclToFullName_4051_: *mut crate::leanh::LeanObject,
    mut v_x_4052_: *mut crate::leanh::LeanObject,
    mut v_x_4053_: usize,
    mut v_x_4054_: usize,
    mut v_x_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: usize = 0;
    let mut v_j_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: usize = 0;
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: usize = 0;
    let mut v___x_4069_: usize = 0;
    let mut v___x_4070_: usize = 0;
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: usize = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: usize = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4088_: u8 = 0;
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: usize = 0;
    let mut v___x_4100_: usize = 0;
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: usize = 0;
    let mut v___x_4103_: usize = 0;
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4052_) == 0 {
                    v_cs_4061_ = crate::leanh::lean_ctor_get(v_x_4052_, 0);
                    crate::leanh::lean_inc_ref(v_cs_4061_);
                    crate::leanh::lean_dec_ref_known(v_x_4052_, 1);
                    v___x_4062_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5___closed__0);
                    v___x_4063_ = lean_usize_shift_right(v_x_4053_, v_x_4054_);
                    v_j_4064_ = lean_usize_to_nat(v___x_4063_);
                    v___x_4065_ = lean_array_get_borrowed(v___x_4062_, v_cs_4061_, v_j_4064_);
                    v___x_4066_ = 1usize;
                    v___x_4067_ = lean_usize_shift_left(v___x_4066_, v_x_4054_);
                    v___x_4068_ = lean_usize_sub(v___x_4067_, v___x_4066_);
                    v___x_4069_ = lean_usize_land(v_x_4053_, v___x_4068_);
                    v___x_4070_ = 5usize;
                    v___x_4071_ = lean_usize_sub(v_x_4054_, v___x_4070_);
                    crate::leanh::lean_inc(v___x_4065_);
                    v___x_4072_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_4051_, v___x_4065_, v___x_4069_, v___x_4071_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                    if crate::leanh::lean_obj_tag(v___x_4072_) == 0 {
                        v_a_4073_ = crate::leanh::lean_ctor_get(v___x_4072_, 0);
                        crate::leanh::lean_inc(v_a_4073_);
                        v___x_4074_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4075_ = lean_nat_add(v_j_4064_, v___x_4074_);
                        crate::leanh::lean_dec(v_j_4064_);
                        v___x_4076_ = lean_array_get_size(v_cs_4061_);
                        v___x_4077_ = lean_nat_dec_lt(v___x_4075_, v___x_4076_);
                        if v___x_4077_ == 0 {
                            crate::leanh::lean_dec(v___x_4075_);
                            crate::leanh::lean_dec(v_a_4073_);
                            crate::leanh::lean_dec_ref(v_cs_4061_);
                            return v___x_4072_;
                        } else {
                            v___x_4078_ = lean_nat_dec_le(v___x_4076_, v___x_4076_);
                            if v___x_4078_ == 0 {
                                if v___x_4077_ == 0 {
                                    crate::leanh::lean_dec(v___x_4075_);
                                    crate::leanh::lean_dec(v_a_4073_);
                                    crate::leanh::lean_dec_ref(v_cs_4061_);
                                    return v___x_4072_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_4072_, 1);
                                    v___x_4079_ = lean_usize_of_nat(v___x_4075_);
                                    crate::leanh::lean_dec(v___x_4075_);
                                    v___x_4080_ = lean_usize_of_nat(v___x_4076_);
                                    v___x_4081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_4051_, v_cs_4061_, v___x_4079_, v___x_4080_, v_a_4073_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                                    crate::leanh::lean_dec_ref(v_cs_4061_);
                                    return v___x_4081_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_4072_, 1);
                                v___x_4082_ = lean_usize_of_nat(v___x_4075_);
                                crate::leanh::lean_dec(v___x_4075_);
                                v___x_4083_ = lean_usize_of_nat(v___x_4076_);
                                v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5_spec__7(v_auxDeclToFullName_4051_, v_cs_4061_, v___x_4082_, v___x_4083_, v_a_4073_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                                crate::leanh::lean_dec_ref(v_cs_4061_);
                                return v___x_4084_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_j_4064_);
                        crate::leanh::lean_dec_ref(v_cs_4061_);
                        return v___x_4072_;
                    }
                } else {
                    v_vs_4085_ = crate::leanh::lean_ctor_get(v_x_4052_, 0);
                    v_isSharedCheck_4105_ = (!crate::leanh::lean_is_exclusive(v_x_4052_)) as u8;
                    if v_isSharedCheck_4105_ == 0 {
                        v___x_4087_ = v_x_4052_;
                        v_isShared_4088_ = v_isSharedCheck_4105_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4085_);
                        crate::leanh::lean_dec(v_x_4052_);
                        v___x_4087_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v___x_4089_);
                    crate::leanh::lean_dec_ref(v_vs_4085_);
                    if v_isShared_4088_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4087_, 0);
                        crate::leanh::lean_ctor_set(v___x_4087_, 0, v_x_4055_);
                        v___x_4093_ = v___x_4087_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_x_4055_);
                        v___x_4093_ = v_reuseFailAlloc_4094_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4095_ = lean_nat_dec_le(v___x_4090_, v___x_4090_);
                    if v___x_4095_ == 0 {
                        if v___x_4091_ == 0 {
                            crate::leanh::lean_dec(v___x_4089_);
                            crate::leanh::lean_dec_ref(v_vs_4085_);
                            if v_isShared_4088_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4087_, 0);
                                crate::leanh::lean_ctor_set(v___x_4087_, 0, v_x_4055_);
                                v___x_4097_ = v___x_4087_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4098_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_x_4055_);
                                v___x_4097_ = v_reuseFailAlloc_4098_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4087_);
                            v___x_4099_ = lean_usize_of_nat(v___x_4089_);
                            crate::leanh::lean_dec(v___x_4089_);
                            v___x_4100_ = lean_usize_of_nat(v___x_4090_);
                            v___x_4101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4051_, v_vs_4085_, v___x_4099_, v___x_4100_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                            crate::leanh::lean_dec_ref(v_vs_4085_);
                            return v___x_4101_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4087_);
                        v___x_4102_ = lean_usize_of_nat(v___x_4089_);
                        crate::leanh::lean_dec(v___x_4089_);
                        v___x_4103_ = lean_usize_of_nat(v___x_4090_);
                        v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4051_, v_vs_4085_, v___x_4102_, v___x_4103_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                        crate::leanh::lean_dec_ref(v_vs_4085_);
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
    mut v_auxDeclToFullName_4106_: *mut crate::leanh::LeanObject,
    mut v_x_4107_: *mut crate::leanh::LeanObject,
    mut v_x_4108_: *mut crate::leanh::LeanObject,
    mut v_x_4109_: *mut crate::leanh::LeanObject,
    mut v_x_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4510__boxed_4116_: usize = 0;
    let mut v_x_4511__boxed_4117_: usize = 0;
    let mut v_res_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4510__boxed_4116_ = crate::leanh::lean_unbox_usize(v_x_4108_);
    crate::leanh::lean_dec(v_x_4108_);
    v_x_4511__boxed_4117_ = crate::leanh::lean_unbox_usize(v_x_4109_);
    crate::leanh::lean_dec(v_x_4109_);
    v_res_4118_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_4106_, v_x_4107_, v_x_4510__boxed_4116_, v_x_4511__boxed_4117_, v_x_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
    crate::leanh::lean_dec(v___y_4114_);
    crate::leanh::lean_dec_ref(v___y_4113_);
    crate::leanh::lean_dec(v___y_4112_);
    crate::leanh::lean_dec_ref(v___y_4111_);
    crate::leanh::lean_dec(v_auxDeclToFullName_4106_);
    return v_res_4118_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(
    mut v_auxDeclToFullName_4119_: *mut crate::leanh::LeanObject,
    mut v_t_4120_: *mut crate::leanh::LeanObject,
    mut v_init_4121_: *mut crate::leanh::LeanObject,
    mut v_start_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: u8 = 0;
    v___x_4128_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4129_ = lean_nat_dec_eq(v_start_4122_, v___x_4128_);
    if v___x_4129_ == 0 {
        let mut v_root_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_4132_: usize = 0;
        let mut v_tailOff_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4134_: u8 = 0;
        v_root_4130_ = crate::leanh::lean_ctor_get(v_t_4120_, 0);
        crate::leanh::lean_inc_ref(v_root_4130_);
        v_tail_4131_ = crate::leanh::lean_ctor_get(v_t_4120_, 1);
        crate::leanh::lean_inc_ref(v_tail_4131_);
        v_shift_4132_ = crate::leanh::lean_ctor_get_usize(v_t_4120_, 4);
        v_tailOff_4133_ = crate::leanh::lean_ctor_get(v_t_4120_, 3);
        crate::leanh::lean_inc(v_tailOff_4133_);
        crate::leanh::lean_dec_ref(v_t_4120_);
        v___x_4134_ = lean_nat_dec_le(v_tailOff_4133_, v_start_4122_);
        if v___x_4134_ == 0 {
            let mut v___x_4135_: usize = 0;
            let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_tailOff_4133_);
            v___x_4135_ = lean_usize_of_nat(v_start_4122_);
            v___x_4136_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_4119_, v_root_4130_, v___x_4135_, v_shift_4132_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
            if crate::leanh::lean_obj_tag(v___x_4136_) == 0 {
                let mut v_a_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4139_: u8 = 0;
                v_a_4137_ = crate::leanh::lean_ctor_get(v___x_4136_, 0);
                crate::leanh::lean_inc(v_a_4137_);
                v___x_4138_ = lean_array_get_size(v_tail_4131_);
                v___x_4139_ = lean_nat_dec_lt(v___x_4128_, v___x_4138_);
                if v___x_4139_ == 0 {
                    crate::leanh::lean_dec(v_a_4137_);
                    crate::leanh::lean_dec_ref(v_tail_4131_);
                    return v___x_4136_;
                } else {
                    let mut v___x_4140_: u8 = 0;
                    v___x_4140_ = lean_nat_dec_le(v___x_4138_, v___x_4138_);
                    if v___x_4140_ == 0 {
                        if v___x_4139_ == 0 {
                            crate::leanh::lean_dec(v_a_4137_);
                            crate::leanh::lean_dec_ref(v_tail_4131_);
                            return v___x_4136_;
                        } else {
                            let mut v___x_4141_: usize = 0;
                            let mut v___x_4142_: usize = 0;
                            let mut v___x_4143_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_4136_, 1);
                            v___x_4141_ = 0usize;
                            v___x_4142_ = lean_usize_of_nat(v___x_4138_);
                            v___x_4143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4141_, v___x_4142_, v_a_4137_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                            crate::leanh::lean_dec_ref(v_tail_4131_);
                            return v___x_4143_;
                        }
                    } else {
                        let mut v___x_4144_: usize = 0;
                        let mut v___x_4145_: usize = 0;
                        let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_4136_, 1);
                        v___x_4144_ = 0usize;
                        v___x_4145_ = lean_usize_of_nat(v___x_4138_);
                        v___x_4146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4144_, v___x_4145_, v_a_4137_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        crate::leanh::lean_dec_ref(v_tail_4131_);
                        return v___x_4146_;
                    }
                }
            } else {
                crate::leanh::lean_dec_ref(v_tail_4131_);
                return v___x_4136_;
            }
        } else {
            let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4149_: u8 = 0;
            crate::leanh::lean_dec_ref(v_root_4130_);
            v___x_4147_ = lean_nat_sub(v_start_4122_, v_tailOff_4133_);
            crate::leanh::lean_dec(v_tailOff_4133_);
            v___x_4148_ = lean_array_get_size(v_tail_4131_);
            v___x_4149_ = lean_nat_dec_lt(v___x_4147_, v___x_4148_);
            if v___x_4149_ == 0 {
                let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_4147_);
                crate::leanh::lean_dec_ref(v_tail_4131_);
                v___x_4150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4150_, 0, v_init_4121_);
                return v___x_4150_;
            } else {
                let mut v___x_4151_: u8 = 0;
                v___x_4151_ = lean_nat_dec_le(v___x_4148_, v___x_4148_);
                if v___x_4151_ == 0 {
                    if v___x_4149_ == 0 {
                        let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v___x_4147_);
                        crate::leanh::lean_dec_ref(v_tail_4131_);
                        v___x_4152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4152_, 0, v_init_4121_);
                        return v___x_4152_;
                    } else {
                        let mut v___x_4153_: usize = 0;
                        let mut v___x_4154_: usize = 0;
                        let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_4153_ = lean_usize_of_nat(v___x_4147_);
                        crate::leanh::lean_dec(v___x_4147_);
                        v___x_4154_ = lean_usize_of_nat(v___x_4148_);
                        v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4153_, v___x_4154_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        crate::leanh::lean_dec_ref(v_tail_4131_);
                        return v___x_4155_;
                    }
                } else {
                    let mut v___x_4156_: usize = 0;
                    let mut v___x_4157_: usize = 0;
                    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_4156_ = lean_usize_of_nat(v___x_4147_);
                    crate::leanh::lean_dec(v___x_4147_);
                    v___x_4157_ = lean_usize_of_nat(v___x_4148_);
                    v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4131_, v___x_4156_, v___x_4157_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                    crate::leanh::lean_dec_ref(v_tail_4131_);
                    return v___x_4158_;
                }
            }
        }
    } else {
        let mut v_root_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_root_4159_ = crate::leanh::lean_ctor_get(v_t_4120_, 0);
        crate::leanh::lean_inc_ref(v_root_4159_);
        v_tail_4160_ = crate::leanh::lean_ctor_get(v_t_4120_, 1);
        crate::leanh::lean_inc_ref(v_tail_4160_);
        crate::leanh::lean_dec_ref(v_t_4120_);
        v___x_4161_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__7(v_auxDeclToFullName_4119_, v_root_4159_, v_init_4121_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
        if crate::leanh::lean_obj_tag(v___x_4161_) == 0 {
            let mut v_a_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4164_: u8 = 0;
            v_a_4162_ = crate::leanh::lean_ctor_get(v___x_4161_, 0);
            crate::leanh::lean_inc(v_a_4162_);
            v___x_4163_ = lean_array_get_size(v_tail_4160_);
            v___x_4164_ = lean_nat_dec_lt(v___x_4128_, v___x_4163_);
            if v___x_4164_ == 0 {
                crate::leanh::lean_dec(v_a_4162_);
                crate::leanh::lean_dec_ref(v_tail_4160_);
                return v___x_4161_;
            } else {
                let mut v___x_4165_: u8 = 0;
                v___x_4165_ = lean_nat_dec_le(v___x_4163_, v___x_4163_);
                if v___x_4165_ == 0 {
                    if v___x_4164_ == 0 {
                        crate::leanh::lean_dec(v_a_4162_);
                        crate::leanh::lean_dec_ref(v_tail_4160_);
                        return v___x_4161_;
                    } else {
                        let mut v___x_4166_: usize = 0;
                        let mut v___x_4167_: usize = 0;
                        let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_4161_, 1);
                        v___x_4166_ = 0usize;
                        v___x_4167_ = lean_usize_of_nat(v___x_4163_);
                        v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4160_, v___x_4166_, v___x_4167_, v_a_4162_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        crate::leanh::lean_dec_ref(v_tail_4160_);
                        return v___x_4168_;
                    }
                } else {
                    let mut v___x_4169_: usize = 0;
                    let mut v___x_4170_: usize = 0;
                    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_4161_, 1);
                    v___x_4169_ = 0usize;
                    v___x_4170_ = lean_usize_of_nat(v___x_4163_);
                    v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__6(v_auxDeclToFullName_4119_, v_tail_4160_, v___x_4169_, v___x_4170_, v_a_4162_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                    crate::leanh::lean_dec_ref(v_tail_4160_);
                    return v___x_4171_;
                }
            }
        } else {
            crate::leanh::lean_dec_ref(v_tail_4160_);
            return v___x_4161_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3___boxed(
    mut v_auxDeclToFullName_4172_: *mut crate::leanh::LeanObject,
    mut v_t_4173_: *mut crate::leanh::LeanObject,
    mut v_init_4174_: *mut crate::leanh::LeanObject,
    mut v_start_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_4172_, v_t_4173_, v_init_4174_, v_start_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
    crate::leanh::lean_dec(v___y_4179_);
    crate::leanh::lean_dec_ref(v___y_4178_);
    crate::leanh::lean_dec(v___y_4177_);
    crate::leanh::lean_dec_ref(v___y_4176_);
    crate::leanh::lean_dec(v_start_4175_);
    crate::leanh::lean_dec(v_auxDeclToFullName_4172_);
    return v_res_4181_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(
    mut v_auxDeclToFullName_4182_: *mut crate::leanh::LeanObject,
    mut v_lctx_4183_: *mut crate::leanh::LeanObject,
    mut v_init_4184_: *mut crate::leanh::LeanObject,
    mut v_start_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_4191_ = crate::leanh::lean_ctor_get(v_lctx_4183_, 1);
    crate::leanh::lean_inc_ref(v_decls_4191_);
    crate::leanh::lean_dec_ref(v_lctx_4183_);
    v___x_4192_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3(v_auxDeclToFullName_4182_, v_decls_4191_, v_init_4184_, v_start_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
    return v___x_4192_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2___boxed(
    mut v_auxDeclToFullName_4193_: *mut crate::leanh::LeanObject,
    mut v_lctx_4194_: *mut crate::leanh::LeanObject,
    mut v_init_4195_: *mut crate::leanh::LeanObject,
    mut v_start_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_4193_, v_lctx_4194_, v_init_4195_, v_start_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    crate::leanh::lean_dec(v___y_4200_);
    crate::leanh::lean_dec_ref(v___y_4199_);
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    crate::leanh::lean_dec(v_start_4196_);
    crate::leanh::lean_dec(v_auxDeclToFullName_4193_);
    return v_res_4202_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4203_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4204_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__0);
    v___x_4205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
    return v___x_4205_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4207_ = lean_mk_empty_array_with_capacity(v___x_4206_);
    v___x_4208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4208_, 0, v___x_4207_);
    return v___x_4208_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4209_: usize = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = 5usize;
    v___x_4210_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4211_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4212_ = lean_mk_empty_array_with_capacity(v___x_4211_);
    v___x_4213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__2);
    v___x_4214_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
    crate::leanh::lean_ctor_set(v___x_4214_, 1, v___x_4212_);
    crate::leanh::lean_ctor_set(v___x_4214_, 2, v___x_4210_);
    crate::leanh::lean_ctor_set(v___x_4214_, 3, v___x_4210_);
    crate::leanh::lean_ctor_set_usize(v___x_4214_, 4, v___x_4209_);
    return v___x_4214_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4215_ = crate::leanh::lean_box(1);
    v___x_4216_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__3);
    v___x_4217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__1);
    v___x_4218_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4218_, 0, v___x_4217_);
    crate::leanh::lean_ctor_set(v___x_4218_, 1, v___x_4216_);
    crate::leanh::lean_ctor_set(v___x_4218_, 2, v___x_4215_);
    return v___x_4218_;
}
pub unsafe fn l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(
    mut v_lctx_4219_: *mut crate::leanh::LeanObject,
    mut v___y_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_auxDeclToFullName_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_auxDeclToFullName_4225_ = crate::leanh::lean_ctor_get(v_lctx_4219_, 2);
    crate::leanh::lean_inc(v_auxDeclToFullName_4225_);
    v___x_4226_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4227_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___closed__4);
    v___x_4228_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2(v_auxDeclToFullName_4225_, v_lctx_4219_, v___x_4227_, v___x_4226_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
    crate::leanh::lean_dec(v_auxDeclToFullName_4225_);
    return v___x_4228_;
}
pub unsafe fn l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0___boxed(
    mut v_lctx_4229_: *mut crate::leanh::LeanObject,
    mut v___y_4230_: *mut crate::leanh::LeanObject,
    mut v___y_4231_: *mut crate::leanh::LeanObject,
    mut v___y_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4235_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(
        v_lctx_4229_,
        v___y_4230_,
        v___y_4231_,
        v___y_4232_,
        v___y_4233_,
    );
    crate::leanh::lean_dec(v___y_4233_);
    crate::leanh::lean_dec_ref(v___y_4232_);
    crate::leanh::lean_dec(v___y_4231_);
    crate::leanh::lean_dec_ref(v___y_4230_);
    return v_res_4235_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(
    mut v_x_4236_: *mut crate::leanh::LeanObject,
    mut v_x_4237_: *mut crate::leanh::LeanObject,
    mut v_x_4238_: *mut crate::leanh::LeanObject,
    mut v_x_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u8 = 0;
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4240_ = crate::leanh::lean_ctor_get(v_x_4236_, 0);
                v_vs_4241_ = crate::leanh::lean_ctor_get(v_x_4236_, 1);
                v_isSharedCheck_4265_ = (!crate::leanh::lean_is_exclusive(v_x_4236_)) as u8;
                if v_isSharedCheck_4265_ == 0 {
                    v___x_4243_ = v_x_4236_;
                    v_isShared_4244_ = v_isSharedCheck_4265_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4241_);
                    crate::leanh::lean_inc(v_ks_4240_);
                    crate::leanh::lean_dec(v_x_4236_);
                    v___x_4243_ = crate::leanh::lean_box(0);
                    v_isShared_4244_ = v_isSharedCheck_4265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4245_ = lean_array_get_size(v_ks_4240_);
                v___x_4246_ = lean_nat_dec_lt(v_x_4237_, v___x_4245_);
                if v___x_4246_ == 0 {
                    crate::leanh::lean_dec(v_x_4237_);
                    v___x_4247_ = lean_array_push(v_ks_4240_, v_x_4238_);
                    v___x_4248_ = lean_array_push(v_vs_4241_, v_x_4239_);
                    if v_isShared_4244_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4243_, 1, v___x_4248_);
                        crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4247_);
                        v___x_4250_ = v___x_4243_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4251_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4247_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 1, v___x_4248_);
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
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_ks_4240_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_vs_4241_);
                            v___x_4255_ = v_reuseFailAlloc_4259_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4260_ = lean_array_fset(v_ks_4240_, v_x_4237_, v_x_4238_);
                        v___x_4261_ = lean_array_fset(v_vs_4241_, v_x_4237_, v_x_4239_);
                        crate::leanh::lean_dec(v_x_4237_);
                        if v_isShared_4244_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4243_, 1, v___x_4261_);
                            crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4260_);
                            v___x_4263_ = v___x_4243_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4264_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4260_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 1, v___x_4261_);
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
                v___x_4256_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4257_ = lean_nat_add(v_x_4237_, v___x_4256_);
                crate::leanh::lean_dec(v_x_4237_);
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
    mut v_n_4266_: *mut crate::leanh::LeanObject,
    mut v_k_4267_: *mut crate::leanh::LeanObject,
    mut v_v_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = crate::leanh::lean_unsigned_to_nat(0);
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
    v___x_4275_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__0);
    v___x_4276_ = lean_usize_sub(v___x_4275_, v___x_4274_);
    return v___x_4276_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4277_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4277_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(
    mut v_x_4278_: *mut crate::leanh::LeanObject,
    mut v_x_4279_: usize,
    mut v_x_4280_: usize,
    mut v_x_4281_: *mut crate::leanh::LeanObject,
    mut v_x_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: usize = 0;
    let mut v___x_4285_: usize = 0;
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: usize = 0;
    let mut v_j_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v_v_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v_node_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4319_: usize = 0;
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4325_: u8 = 0;
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4327_: u8 = 0;
    let mut v_unused_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: u8 = 0;
    let mut v_ks_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: usize = 0;
    let mut v___x_4345_: u8 = 0;
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: u8 = 0;
    let mut v_reuseFailAlloc_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4278_) == 0 {
                    v_es_4283_ = crate::leanh::lean_ctor_get(v_x_4278_, 0);
                    v___x_4284_ = 5usize;
                    v___x_4285_ = 1usize;
                    v___x_4286_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__1);
                    v___x_4287_ = lean_usize_land(v_x_4279_, v___x_4286_);
                    v_j_4288_ = lean_usize_to_nat(v___x_4287_);
                    v___x_4289_ = lean_array_get_size(v_es_4283_);
                    v___x_4290_ = lean_nat_dec_lt(v_j_4288_, v___x_4289_);
                    if v___x_4290_ == 0 {
                        crate::leanh::lean_dec(v_j_4288_);
                        crate::leanh::lean_dec(v_x_4282_);
                        crate::leanh::lean_dec(v_x_4281_);
                        return v_x_4278_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4283_);
                        v_isSharedCheck_4327_ = (!crate::leanh::lean_is_exclusive(v_x_4278_)) as u8;
                        if v_isSharedCheck_4327_ == 0 {
                            v_unused_4328_ = crate::leanh::lean_ctor_get(v_x_4278_, 0);
                            crate::leanh::lean_dec(v_unused_4328_);
                            v___x_4292_ = v_x_4278_;
                            v_isShared_4293_ = v_isSharedCheck_4327_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4278_);
                            v___x_4292_ = crate::leanh::lean_box(0);
                            v_isShared_4293_ = v_isSharedCheck_4327_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4329_ = crate::leanh::lean_ctor_get(v_x_4278_, 0);
                    v_vs_4330_ = crate::leanh::lean_ctor_get(v_x_4278_, 1);
                    v_isSharedCheck_4350_ = (!crate::leanh::lean_is_exclusive(v_x_4278_)) as u8;
                    if v_isSharedCheck_4350_ == 0 {
                        v___x_4332_ = v_x_4278_;
                        v_isShared_4333_ = v_isSharedCheck_4350_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4330_);
                        crate::leanh::lean_inc(v_ks_4329_);
                        crate::leanh::lean_dec(v_x_4278_);
                        v___x_4332_ = crate::leanh::lean_box(0);
                        v_isShared_4333_ = v_isSharedCheck_4350_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4294_ = lean_array_fget(v_es_4283_, v_j_4288_);
                v___x_4295_ = crate::leanh::lean_box(0);
                v_xs_x27_4296_ = lean_array_fset(v_es_4283_, v_j_4288_, v___x_4295_);
                match crate::leanh::lean_obj_tag(v_v_4294_) {
                    0 => {
                        v_key_4303_ = crate::leanh::lean_ctor_get(v_v_4294_, 0);
                        v_val_4304_ = crate::leanh::lean_ctor_get(v_v_4294_, 1);
                        v_isSharedCheck_4314_ = (!crate::leanh::lean_is_exclusive(v_v_4294_)) as u8;
                        if v_isSharedCheck_4314_ == 0 {
                            v___x_4306_ = v_v_4294_;
                            v_isShared_4307_ = v_isSharedCheck_4314_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4304_);
                            crate::leanh::lean_inc(v_key_4303_);
                            crate::leanh::lean_dec(v_v_4294_);
                            v___x_4306_ = crate::leanh::lean_box(0);
                            v_isShared_4307_ = v_isSharedCheck_4314_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4315_ = crate::leanh::lean_ctor_get(v_v_4294_, 0);
                        v_isSharedCheck_4325_ = (!crate::leanh::lean_is_exclusive(v_v_4294_)) as u8;
                        if v_isSharedCheck_4325_ == 0 {
                            v___x_4317_ = v_v_4294_;
                            v_isShared_4318_ = v_isSharedCheck_4325_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4315_);
                            crate::leanh::lean_dec(v_v_4294_);
                            v___x_4317_ = crate::leanh::lean_box(0);
                            v_isShared_4318_ = v_isSharedCheck_4325_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4326_, 0, v_x_4281_);
                        crate::leanh::lean_ctor_set(v___x_4326_, 1, v_x_4282_);
                        v___y_4298_ = v___x_4326_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4299_ = lean_array_fset(v_xs_x27_4296_, v_j_4288_, v___y_4298_);
                crate::leanh::lean_dec(v_j_4288_);
                if v_isShared_4293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4292_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
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
                    crate::leanh::lean_del_object(v___x_4306_);
                    v___x_4309_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4303_,
                        v_val_4304_,
                        v_x_4281_,
                        v_x_4282_,
                    );
                    v___x_4310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4310_, 0, v___x_4309_);
                    v___y_4298_ = v___x_4310_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4304_);
                    crate::leanh::lean_dec(v_key_4303_);
                    if v_isShared_4307_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4306_, 1, v_x_4282_);
                        crate::leanh::lean_ctor_set(v___x_4306_, 0, v_x_4281_);
                        v___x_4312_ = v___x_4306_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_x_4281_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_x_4282_);
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
                    crate::leanh::lean_ctor_set(v___x_4317_, 0, v___x_4321_);
                    v___x_4323_ = v___x_4317_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
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
                    v_reuseFailAlloc_4349_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_ks_4329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4349_, 1, v_vs_4330_);
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
                    v___x_4347_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4348_ = lean_nat_dec_lt(v___x_4346_, v___x_4347_);
                    crate::leanh::lean_dec(v___x_4346_);
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
                    v_ks_4339_ = crate::leanh::lean_ctor_get(v_newNode_4336_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4339_);
                    v_vs_4340_ = crate::leanh::lean_ctor_get(v_newNode_4336_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4340_);
                    crate::leanh::lean_dec_ref(v_newNode_4336_);
                    v___x_4341_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___closed__2);
                    v___x_4343_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_x_4280_, v_ks_4339_, v_vs_4340_, v___x_4341_, v___x_4342_);
                    crate::leanh::lean_dec_ref(v_vs_4340_);
                    crate::leanh::lean_dec_ref(v_ks_4339_);
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
    mut v_keys_4352_: *mut crate::leanh::LeanObject,
    mut v_vals_4353_: *mut crate::leanh::LeanObject,
    mut v_i_4354_: *mut crate::leanh::LeanObject,
    mut v_entries_4355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v_k_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u64 = 0;
    let mut v_h_4361_: usize = 0;
    let mut v___x_4362_: usize = 0;
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: usize = 0;
    let mut v___x_4365_: usize = 0;
    let mut v___x_4366_: usize = 0;
    let mut v_h_4367_: usize = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4356_ = lean_array_get_size(v_keys_4352_);
                v___x_4357_ = lean_nat_dec_lt(v_i_4354_, v___x_4356_);
                if v___x_4357_ == 0 {
                    crate::leanh::lean_dec(v_i_4354_);
                    return v_entries_4355_;
                } else {
                    v_k_4358_ = lean_array_fget_borrowed(v_keys_4352_, v_i_4354_);
                    v_v_4359_ = lean_array_fget_borrowed(v_vals_4353_, v_i_4354_);
                    v___x_4360_ = l_Lean_instHashableMVarId_hash(v_k_4358_);
                    v_h_4361_ = lean_uint64_to_usize(v___x_4360_);
                    v___x_4362_ = 5usize;
                    v___x_4363_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4364_ = 1usize;
                    v___x_4365_ = lean_usize_sub(v_depth_4351_, v___x_4364_);
                    v___x_4366_ = lean_usize_mul(v___x_4362_, v___x_4365_);
                    v_h_4367_ = lean_usize_shift_right(v_h_4361_, v___x_4366_);
                    v___x_4368_ = lean_nat_add(v_i_4354_, v___x_4363_);
                    crate::leanh::lean_dec(v_i_4354_);
                    crate::leanh::lean_inc(v_v_4359_);
                    crate::leanh::lean_inc(v_k_4358_);
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
    mut v_depth_4371_: *mut crate::leanh::LeanObject,
    mut v_keys_4372_: *mut crate::leanh::LeanObject,
    mut v_vals_4373_: *mut crate::leanh::LeanObject,
    mut v_i_4374_: *mut crate::leanh::LeanObject,
    mut v_entries_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4376_: usize = 0;
    let mut v_res_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4376_ = crate::leanh::lean_unbox_usize(v_depth_4371_);
    crate::leanh::lean_dec(v_depth_4371_);
    v_res_4377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_boxed_4376_, v_keys_4372_, v_vals_4373_, v_i_4374_, v_entries_4375_);
    crate::leanh::lean_dec_ref(v_vals_4373_);
    crate::leanh::lean_dec_ref(v_keys_4372_);
    return v_res_4377_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_x_4378_: *mut crate::leanh::LeanObject,
    mut v_x_4379_: *mut crate::leanh::LeanObject,
    mut v_x_4380_: *mut crate::leanh::LeanObject,
    mut v_x_4381_: *mut crate::leanh::LeanObject,
    mut v_x_4382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4896__boxed_4383_: usize = 0;
    let mut v_x_4897__boxed_4384_: usize = 0;
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4896__boxed_4383_ = crate::leanh::lean_unbox_usize(v_x_4379_);
    crate::leanh::lean_dec(v_x_4379_);
    v_x_4897__boxed_4384_ = crate::leanh::lean_unbox_usize(v_x_4380_);
    crate::leanh::lean_dec(v_x_4380_);
    v_res_4385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_4378_, v_x_4896__boxed_4383_, v_x_4897__boxed_4384_, v_x_4381_, v_x_4382_);
    return v_res_4385_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(
    mut v_x_4386_: *mut crate::leanh::LeanObject,
    mut v_x_4387_: *mut crate::leanh::LeanObject,
    mut v_x_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4389_: u64 = 0;
    let mut v___x_4390_: usize = 0;
    let mut v___x_4391_: usize = 0;
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_instHashableMVarId_hash(v_x_4387_);
    v___x_4390_ = lean_uint64_to_usize(v___x_4389_);
    v___x_4391_ = 1usize;
    v___x_4392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_4386_, v___x_4390_, v___x_4391_, v_x_4387_, v_x_4388_);
    return v___x_4392_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(
    mut v_mvarId_4393_: *mut crate::leanh::LeanObject,
    mut v_val_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4405_: u8 = 0;
    let mut v_depth_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4429_: u8 = 0;
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4397_ = lean_st_ref_take(v___y_4395_);
                v_mctx_4398_ = crate::leanh::lean_ctor_get(v___x_4397_, 0);
                v_cache_4399_ = crate::leanh::lean_ctor_get(v___x_4397_, 1);
                v_zetaDeltaFVarIds_4400_ = crate::leanh::lean_ctor_get(v___x_4397_, 2);
                v_postponed_4401_ = crate::leanh::lean_ctor_get(v___x_4397_, 3);
                v_diag_4402_ = crate::leanh::lean_ctor_get(v___x_4397_, 4);
                v_isSharedCheck_4430_ = (!crate::leanh::lean_is_exclusive(v___x_4397_)) as u8;
                if v_isSharedCheck_4430_ == 0 {
                    v___x_4404_ = v___x_4397_;
                    v_isShared_4405_ = v_isSharedCheck_4430_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4402_);
                    crate::leanh::lean_inc(v_postponed_4401_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4400_);
                    crate::leanh::lean_inc(v_cache_4399_);
                    crate::leanh::lean_inc(v_mctx_4398_);
                    crate::leanh::lean_dec(v___x_4397_);
                    v___x_4404_ = crate::leanh::lean_box(0);
                    v_isShared_4405_ = v_isSharedCheck_4430_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4406_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 0);
                v_levelAssignDepth_4407_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 1);
                v_lmvarCounter_4408_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 2);
                v_mvarCounter_4409_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 3);
                v_lDecls_4410_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 4);
                v_decls_4411_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 5);
                v_userNames_4412_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 6);
                v_lAssignment_4413_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 7);
                v_eAssignment_4414_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 8);
                v_dAssignment_4415_ = crate::leanh::lean_ctor_get(v_mctx_4398_, 9);
                v_isSharedCheck_4429_ = (!crate::leanh::lean_is_exclusive(v_mctx_4398_)) as u8;
                if v_isSharedCheck_4429_ == 0 {
                    v___x_4417_ = v_mctx_4398_;
                    v_isShared_4418_ = v_isSharedCheck_4429_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_4415_);
                    crate::leanh::lean_inc(v_eAssignment_4414_);
                    crate::leanh::lean_inc(v_lAssignment_4413_);
                    crate::leanh::lean_inc(v_userNames_4412_);
                    crate::leanh::lean_inc(v_decls_4411_);
                    crate::leanh::lean_inc(v_lDecls_4410_);
                    crate::leanh::lean_inc(v_mvarCounter_4409_);
                    crate::leanh::lean_inc(v_lmvarCounter_4408_);
                    crate::leanh::lean_inc(v_levelAssignDepth_4407_);
                    crate::leanh::lean_inc(v_depth_4406_);
                    crate::leanh::lean_dec(v_mctx_4398_);
                    v___x_4417_ = crate::leanh::lean_box(0);
                    v_isShared_4418_ = v_isSharedCheck_4429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4419_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_4414_, v_mvarId_4393_, v_val_4394_);
                if v_isShared_4418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4417_, 8, v___x_4419_);
                    v___x_4421_ = v___x_4417_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4428_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_depth_4406_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4428_,
                        1,
                        v_levelAssignDepth_4407_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_lmvarCounter_4408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 3, v_mvarCounter_4409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 4, v_lDecls_4410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 5, v_decls_4411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 6, v_userNames_4412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 7, v_lAssignment_4413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 8, v___x_4419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 9, v_dAssignment_4415_);
                    v___x_4421_ = v_reuseFailAlloc_4428_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4404_, 0, v___x_4421_);
                    v___x_4423_ = v___x_4404_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4427_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_cache_4399_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4427_,
                        2,
                        v_zetaDeltaFVarIds_4400_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 3, v_postponed_4401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4427_, 4, v_diag_4402_);
                    v___x_4423_ = v_reuseFailAlloc_4427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4424_ = lean_st_ref_set(v___y_4395_, v___x_4423_);
                v___x_4425_ = crate::leanh::lean_box(0);
                v___x_4426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4426_, 0, v___x_4425_);
                return v___x_4426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(
    mut v_mvarId_4431_: *mut crate::leanh::LeanObject,
    mut v_val_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(
        v_mvarId_4431_,
        v_val_4432_,
        v___y_4433_,
    );
    crate::leanh::lean_dec(v___y_4433_);
    return v_res_4435_;
}
pub unsafe fn l_Lean_MVarId_instantiateGoalMVars(
    mut v_mvarId_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
    mut v_a_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_unused_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_a_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_a_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut v_a_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4442_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                crate::leanh::lean_inc(v_mvarId_4436_);
                v___x_4443_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4436_,
                    v___x_4442_,
                    v_a_4437_,
                    v_a_4438_,
                    v_a_4439_,
                    v_a_4440_,
                );
                if crate::leanh::lean_obj_tag(v___x_4443_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4443_, 1);
                    crate::leanh::lean_inc(v_mvarId_4436_);
                    v___x_4444_ = l_Lean_MVarId_getDecl(
                        v_mvarId_4436_,
                        v_a_4437_,
                        v_a_4438_,
                        v_a_4439_,
                        v_a_4440_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4444_) == 0 {
                        v_a_4445_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                        crate::leanh::lean_inc(v_a_4445_);
                        crate::leanh::lean_dec_ref_known(v___x_4444_, 1);
                        v_userName_4446_ = crate::leanh::lean_ctor_get(v_a_4445_, 0);
                        crate::leanh::lean_inc(v_userName_4446_);
                        v_lctx_4447_ = crate::leanh::lean_ctor_get(v_a_4445_, 1);
                        crate::leanh::lean_inc_ref(v_lctx_4447_);
                        v_type_4448_ = crate::leanh::lean_ctor_get(v_a_4445_, 2);
                        crate::leanh::lean_inc_ref(v_type_4448_);
                        v_localInstances_4449_ = crate::leanh::lean_ctor_get(v_a_4445_, 4);
                        crate::leanh::lean_inc_ref(v_localInstances_4449_);
                        crate::leanh::lean_dec(v_a_4445_);
                        v___x_4450_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_4447_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_);
                        if crate::leanh::lean_obj_tag(v___x_4450_) == 0 {
                            v_a_4451_ = crate::leanh::lean_ctor_get(v___x_4450_, 0);
                            crate::leanh::lean_inc(v_a_4451_);
                            crate::leanh::lean_dec_ref_known(v___x_4450_, 1);
                            v___x_4452_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_4448_, v_a_4438_);
                            v_a_4453_ = crate::leanh::lean_ctor_get(v___x_4452_, 0);
                            crate::leanh::lean_inc(v_a_4453_);
                            crate::leanh::lean_dec_ref(v___x_4452_);
                            v___x_4454_ = 2;
                            v___x_4455_ = crate::leanh::lean_unsigned_to_nat(0);
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
                            if crate::leanh::lean_obj_tag(v___x_4456_) == 0 {
                                v_a_4457_ = crate::leanh::lean_ctor_get(v___x_4456_, 0);
                                crate::leanh::lean_inc_n(v_a_4457_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_4456_, 1);
                                v___x_4458_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_4436_, v_a_4457_, v_a_4438_);
                                v_isSharedCheck_4466_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4458_)) as u8;
                                if v_isSharedCheck_4466_ == 0 {
                                    v_unused_4467_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                                    crate::leanh::lean_dec(v_unused_4467_);
                                    v___x_4460_ = v___x_4458_;
                                    v_isShared_4461_ = v_isSharedCheck_4466_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4458_);
                                    v___x_4460_ = crate::leanh::lean_box(0);
                                    v_isShared_4461_ = v_isSharedCheck_4466_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_mvarId_4436_);
                                v_a_4468_ = crate::leanh::lean_ctor_get(v___x_4456_, 0);
                                v_isSharedCheck_4475_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4456_)) as u8;
                                if v_isSharedCheck_4475_ == 0 {
                                    v___x_4470_ = v___x_4456_;
                                    v_isShared_4471_ = v_isSharedCheck_4475_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4468_);
                                    crate::leanh::lean_dec(v___x_4456_);
                                    v___x_4470_ = crate::leanh::lean_box(0);
                                    v_isShared_4471_ = v_isSharedCheck_4475_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_localInstances_4449_);
                            crate::leanh::lean_dec_ref(v_type_4448_);
                            crate::leanh::lean_dec(v_userName_4446_);
                            crate::leanh::lean_dec(v_mvarId_4436_);
                            v_a_4476_ = crate::leanh::lean_ctor_get(v___x_4450_, 0);
                            v_isSharedCheck_4483_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4450_)) as u8;
                            if v_isSharedCheck_4483_ == 0 {
                                v___x_4478_ = v___x_4450_;
                                v_isShared_4479_ = v_isSharedCheck_4483_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4476_);
                                crate::leanh::lean_dec(v___x_4450_);
                                v___x_4478_ = crate::leanh::lean_box(0);
                                v_isShared_4479_ = v_isSharedCheck_4483_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_4436_);
                        v_a_4484_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                        v_isSharedCheck_4491_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4444_)) as u8;
                        if v_isSharedCheck_4491_ == 0 {
                            v___x_4486_ = v___x_4444_;
                            v_isShared_4487_ = v_isSharedCheck_4491_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4484_);
                            crate::leanh::lean_dec(v___x_4444_);
                            v___x_4486_ = crate::leanh::lean_box(0);
                            v_isShared_4487_ = v_isSharedCheck_4491_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4436_);
                    v_a_4492_ = crate::leanh::lean_ctor_get(v___x_4443_, 0);
                    v_isSharedCheck_4499_ = (!crate::leanh::lean_is_exclusive(v___x_4443_)) as u8;
                    if v_isSharedCheck_4499_ == 0 {
                        v___x_4494_ = v___x_4443_;
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4492_);
                        crate::leanh::lean_dec(v___x_4443_);
                        v___x_4494_ = crate::leanh::lean_box(0);
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4462_ = l_Lean_Expr_mvarId_x21(v_a_4457_);
                crate::leanh::lean_dec(v_a_4457_);
                if v_isShared_4461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4460_, 0, v___x_4462_);
                    v___x_4464_ = v___x_4460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
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
                    v_reuseFailAlloc_4474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
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
                    v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
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
                    v_reuseFailAlloc_4490_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
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
                    v_reuseFailAlloc_4498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
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
    mut v_mvarId_4500_: *mut crate::leanh::LeanObject,
    mut v_a_4501_: *mut crate::leanh::LeanObject,
    mut v_a_4502_: *mut crate::leanh::LeanObject,
    mut v_a_4503_: *mut crate::leanh::LeanObject,
    mut v_a_4504_: *mut crate::leanh::LeanObject,
    mut v_a_4505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4506_ = l_Lean_MVarId_instantiateGoalMVars(
        v_mvarId_4500_,
        v_a_4501_,
        v_a_4502_,
        v_a_4503_,
        v_a_4504_,
    );
    crate::leanh::lean_dec(v_a_4504_);
    crate::leanh::lean_dec_ref(v_a_4503_);
    crate::leanh::lean_dec(v_a_4502_);
    crate::leanh::lean_dec_ref(v_a_4501_);
    return v_res_4506_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(
    mut v_mvarId_4507_: *mut crate::leanh::LeanObject,
    mut v_val_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4514_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(
        v_mvarId_4507_,
        v_val_4508_,
        v___y_4510_,
    );
    return v___x_4514_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(
    mut v_mvarId_4515_: *mut crate::leanh::LeanObject,
    mut v_val_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4522_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(
        v_mvarId_4515_,
        v_val_4516_,
        v___y_4517_,
        v___y_4518_,
        v___y_4519_,
        v___y_4520_,
    );
    crate::leanh::lean_dec(v___y_4520_);
    crate::leanh::lean_dec_ref(v___y_4519_);
    crate::leanh::lean_dec(v___y_4518_);
    crate::leanh::lean_dec_ref(v___y_4517_);
    return v_res_4522_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(
    mut v_00_u03b4_4523_: *mut crate::leanh::LeanObject,
    mut v_t_4524_: *mut crate::leanh::LeanObject,
    mut v_k_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_4524_, v_k_4525_);
    return v___x_4526_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(
    mut v_00_u03b4_4527_: *mut crate::leanh::LeanObject,
    mut v_t_4528_: *mut crate::leanh::LeanObject,
    mut v_k_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_4527_, v_t_4528_, v_k_4529_);
    crate::leanh::lean_dec(v_k_4529_);
    crate::leanh::lean_dec(v_t_4528_);
    return v_res_4530_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(
    mut v_00_u03b2_4531_: *mut crate::leanh::LeanObject,
    mut v_x_4532_: *mut crate::leanh::LeanObject,
    mut v_x_4533_: *mut crate::leanh::LeanObject,
    mut v_x_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_4532_, v_x_4533_, v_x_4534_);
    return v___x_4535_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(
    mut v_00_u03b2_4536_: *mut crate::leanh::LeanObject,
    mut v_x_4537_: *mut crate::leanh::LeanObject,
    mut v_x_4538_: usize,
    mut v_x_4539_: usize,
    mut v_x_4540_: *mut crate::leanh::LeanObject,
    mut v_x_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_4537_, v_x_4538_, v_x_4539_, v_x_4540_, v_x_4541_);
    return v___x_4542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b2_4543_: *mut crate::leanh::LeanObject,
    mut v_x_4544_: *mut crate::leanh::LeanObject,
    mut v_x_4545_: *mut crate::leanh::LeanObject,
    mut v_x_4546_: *mut crate::leanh::LeanObject,
    mut v_x_4547_: *mut crate::leanh::LeanObject,
    mut v_x_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5262__boxed_4549_: usize = 0;
    let mut v_x_5263__boxed_4550_: usize = 0;
    let mut v_res_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5262__boxed_4549_ = crate::leanh::lean_unbox_usize(v_x_4545_);
    crate::leanh::lean_dec(v_x_4545_);
    v_x_5263__boxed_4550_ = crate::leanh::lean_unbox_usize(v_x_4546_);
    crate::leanh::lean_dec(v_x_4546_);
    v_res_4551_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_4543_, v_x_4544_, v_x_5262__boxed_4549_, v_x_5263__boxed_4550_, v_x_4547_, v_x_4548_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(
    mut v_00_u03b2_4552_: *mut crate::leanh::LeanObject,
    mut v_n_4553_: *mut crate::leanh::LeanObject,
    mut v_k_4554_: *mut crate::leanh::LeanObject,
    mut v_v_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_4553_, v_k_4554_, v_v_4555_);
    return v___x_4556_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(
    mut v_00_u03b2_4557_: *mut crate::leanh::LeanObject,
    mut v_depth_4558_: usize,
    mut v_keys_4559_: *mut crate::leanh::LeanObject,
    mut v_vals_4560_: *mut crate::leanh::LeanObject,
    mut v_heq_4561_: *mut crate::leanh::LeanObject,
    mut v_i_4562_: *mut crate::leanh::LeanObject,
    mut v_entries_4563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4564_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_4558_, v_keys_4559_, v_vals_4560_, v_i_4562_, v_entries_4563_);
    return v___x_4564_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(
    mut v_00_u03b2_4565_: *mut crate::leanh::LeanObject,
    mut v_depth_4566_: *mut crate::leanh::LeanObject,
    mut v_keys_4567_: *mut crate::leanh::LeanObject,
    mut v_vals_4568_: *mut crate::leanh::LeanObject,
    mut v_heq_4569_: *mut crate::leanh::LeanObject,
    mut v_i_4570_: *mut crate::leanh::LeanObject,
    mut v_entries_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4572_: usize = 0;
    let mut v_res_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4572_ = crate::leanh::lean_unbox_usize(v_depth_4566_);
    crate::leanh::lean_dec(v_depth_4566_);
    v_res_4573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_4565_, v_depth_boxed_4572_, v_keys_4567_, v_vals_4568_, v_heq_4569_, v_i_4570_, v_entries_4571_);
    crate::leanh::lean_dec_ref(v_vals_4568_);
    crate::leanh::lean_dec_ref(v_keys_4567_);
    return v_res_4573_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(
    mut v_00_u03b2_4574_: *mut crate::leanh::LeanObject,
    mut v_x_4575_: *mut crate::leanh::LeanObject,
    mut v_x_4576_: *mut crate::leanh::LeanObject,
    mut v_x_4577_: *mut crate::leanh::LeanObject,
    mut v_x_4578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4579_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_4575_, v_x_4576_, v_x_4577_, v_x_4578_);
    return v___x_4579_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(
    mut v_k_4580_: *mut crate::leanh::LeanObject,
    mut v_b_4581_: *mut crate::leanh::LeanObject,
    mut v_c_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4586_);
    crate::leanh::lean_inc_ref(v___y_4585_);
    crate::leanh::lean_inc(v___y_4584_);
    crate::leanh::lean_inc_ref(v___y_4583_);
    v___x_4588_ = crate::leanh::lean_apply_7(
        v_k_4580_,
        v_b_4581_,
        v_c_4582_,
        v___y_4583_,
        v___y_4584_,
        v___y_4585_,
        v___y_4586_,
        crate::leanh::lean_box(0),
    );
    return v___x_4588_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(
    mut v_k_4589_: *mut crate::leanh::LeanObject,
    mut v_b_4590_: *mut crate::leanh::LeanObject,
    mut v_c_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
    mut v___y_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4595_);
    crate::leanh::lean_dec_ref(v___y_4594_);
    crate::leanh::lean_dec(v___y_4593_);
    crate::leanh::lean_dec_ref(v___y_4592_);
    return v_res_4597_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(
    mut v_e_4598_: *mut crate::leanh::LeanObject,
    mut v_k_4599_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4600_: u8,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: u8 = 0;
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4606_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4606_, 0, v_k_4599_);
                v___x_4607_ = 1;
                v___x_4608_ = 0;
                v___x_4609_ = crate::leanh::lean_box(0);
                v___x_4610_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
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
                if crate::leanh::lean_obj_tag(v___x_4610_) == 0 {
                    v_a_4611_ = crate::leanh::lean_ctor_get(v___x_4610_, 0);
                    v_isSharedCheck_4618_ = (!crate::leanh::lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4613_ = v___x_4610_;
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4611_);
                        crate::leanh::lean_dec(v___x_4610_);
                        v___x_4613_ = crate::leanh::lean_box(0);
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4619_ = crate::leanh::lean_ctor_get(v___x_4610_, 0);
                    v_isSharedCheck_4626_ = (!crate::leanh::lean_is_exclusive(v___x_4610_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4610_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4619_);
                        crate::leanh::lean_dec(v___x_4610_);
                        v___x_4621_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
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
                    v_reuseFailAlloc_4625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
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
    mut v_e_4627_: *mut crate::leanh::LeanObject,
    mut v_k_4628_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4635_: u8 = 0;
    let mut v_res_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4635_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4629_) as u8);
    v_res_4636_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(
        v_e_4627_,
        v_k_4628_,
        v_cleanupAnnotations_boxed_4635_,
        v___y_4630_,
        v___y_4631_,
        v___y_4632_,
        v___y_4633_,
    );
    crate::leanh::lean_dec(v___y_4633_);
    crate::leanh::lean_dec_ref(v___y_4632_);
    crate::leanh::lean_dec(v___y_4631_);
    crate::leanh::lean_dec_ref(v___y_4630_);
    return v_res_4636_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(
    mut v_00_u03b1_4637_: *mut crate::leanh::LeanObject,
    mut v_e_4638_: *mut crate::leanh::LeanObject,
    mut v_k_4639_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4640_: u8,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
    mut v___y_4642_: *mut crate::leanh::LeanObject,
    mut v___y_4643_: *mut crate::leanh::LeanObject,
    mut v___y_4644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4647_: *mut crate::leanh::LeanObject,
    mut v_e_4648_: *mut crate::leanh::LeanObject,
    mut v_k_4649_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4656_: u8 = 0;
    let mut v_res_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4656_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4650_) as u8);
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
    crate::leanh::lean_dec(v___y_4654_);
    crate::leanh::lean_dec_ref(v___y_4653_);
    crate::leanh::lean_dec(v___y_4652_);
    crate::leanh::lean_dec_ref(v___y_4651_);
    return v_res_4657_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
    mut v_mvarId_4658_: *mut crate::leanh::LeanObject,
    mut v_x_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4669_: u8 = 0;
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_a_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4658_,
                    v_x_4659_,
                    v___y_4660_,
                    v___y_4661_,
                    v___y_4662_,
                    v___y_4663_,
                );
                if crate::leanh::lean_obj_tag(v___x_4665_) == 0 {
                    v_a_4666_ = crate::leanh::lean_ctor_get(v___x_4665_, 0);
                    v_isSharedCheck_4673_ = (!crate::leanh::lean_is_exclusive(v___x_4665_)) as u8;
                    if v_isSharedCheck_4673_ == 0 {
                        v___x_4668_ = v___x_4665_;
                        v_isShared_4669_ = v_isSharedCheck_4673_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4666_);
                        crate::leanh::lean_dec(v___x_4665_);
                        v___x_4668_ = crate::leanh::lean_box(0);
                        v_isShared_4669_ = v_isSharedCheck_4673_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4674_ = crate::leanh::lean_ctor_get(v___x_4665_, 0);
                    v_isSharedCheck_4681_ = (!crate::leanh::lean_is_exclusive(v___x_4665_)) as u8;
                    if v_isSharedCheck_4681_ == 0 {
                        v___x_4676_ = v___x_4665_;
                        v_isShared_4677_ = v_isSharedCheck_4681_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4674_);
                        crate::leanh::lean_dec(v___x_4665_);
                        v___x_4676_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
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
                    v_reuseFailAlloc_4680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
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
    mut v_mvarId_4682_: *mut crate::leanh::LeanObject,
    mut v_x_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4689_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(
        v_mvarId_4682_,
        v_x_4683_,
        v___y_4684_,
        v___y_4685_,
        v___y_4686_,
        v___y_4687_,
    );
    crate::leanh::lean_dec(v___y_4687_);
    crate::leanh::lean_dec_ref(v___y_4686_);
    crate::leanh::lean_dec(v___y_4685_);
    crate::leanh::lean_dec_ref(v___y_4684_);
    return v_res_4689_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(
    mut v_00_u03b1_4690_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4691_: *mut crate::leanh::LeanObject,
    mut v_x_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4699_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4700_: *mut crate::leanh::LeanObject,
    mut v_x_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(
        v_00_u03b1_4699_,
        v_mvarId_4700_,
        v_x_4701_,
        v___y_4702_,
        v___y_4703_,
        v___y_4704_,
        v___y_4705_,
    );
    crate::leanh::lean_dec(v___y_4705_);
    crate::leanh::lean_dec_ref(v___y_4704_);
    crate::leanh::lean_dec(v___y_4703_);
    crate::leanh::lean_dec_ref(v___y_4702_);
    return v_res_4707_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars___lam__0(
    mut v___x_4708_: u8,
    mut v___x_4709_: u8,
    mut v_xs_4710_: *mut crate::leanh::LeanObject,
    mut v_body_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
    mut v___y_4714_: *mut crate::leanh::LeanObject,
    mut v___y_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_4719_: *mut crate::leanh::LeanObject,
    mut v___x_4720_: *mut crate::leanh::LeanObject,
    mut v_xs_4721_: *mut crate::leanh::LeanObject,
    mut v_body_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1951__boxed_4728_: u8 = 0;
    let mut v___x_1952__boxed_4729_: u8 = 0;
    let mut v_res_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1951__boxed_4728_ = (crate::leanh::lean_unbox(v___x_4719_) as u8);
    v___x_1952__boxed_4729_ = (crate::leanh::lean_unbox(v___x_4720_) as u8);
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
    crate::leanh::lean_dec(v___y_4726_);
    crate::leanh::lean_dec_ref(v___y_4725_);
    crate::leanh::lean_dec(v___y_4724_);
    crate::leanh::lean_dec_ref(v___y_4723_);
    crate::leanh::lean_dec_ref(v_xs_4721_);
    return v_res_4730_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars___lam__1(
    mut v_a_4731_: *mut crate::leanh::LeanObject,
    mut v___x_4732_: u8,
    mut v___f_4733_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4759_: u8 = 0;
    let mut v_unused_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4768_: u8 = 0;
    let mut v_a_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4772_: u8 = 0;
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4776_: u8 = 0;
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4784_: u8 = 0;
    let mut v_a_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4788_: u8 = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_4740_) == 0 {
                    v_a_4741_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                    crate::leanh::lean_inc(v_a_4741_);
                    crate::leanh::lean_dec_ref_known(v___x_4740_, 1);
                    v_mvars_4742_ = crate::leanh::lean_ctor_get(v_a_4741_, 1);
                    crate::leanh::lean_inc_ref(v_mvars_4742_);
                    v_expr_4743_ = crate::leanh::lean_ctor_get(v_a_4741_, 2);
                    crate::leanh::lean_inc_ref(v_expr_4743_);
                    crate::leanh::lean_dec(v_a_4741_);
                    v___x_4744_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_4743_, v___f_4733_, v___x_4732_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
                    if crate::leanh::lean_obj_tag(v___x_4744_) == 0 {
                        v_a_4745_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        crate::leanh::lean_inc(v_a_4745_);
                        crate::leanh::lean_dec_ref_known(v___x_4744_, 1);
                        crate::leanh::lean_inc(v_mvarId_4734_);
                        v___x_4746_ = l_Lean_MVarId_getTag(
                            v_mvarId_4734_,
                            v___y_4735_,
                            v___y_4736_,
                            v___y_4737_,
                            v___y_4738_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4746_) == 0 {
                            v_a_4747_ = crate::leanh::lean_ctor_get(v___x_4746_, 0);
                            crate::leanh::lean_inc(v_a_4747_);
                            crate::leanh::lean_dec_ref_known(v___x_4746_, 1);
                            v___x_4748_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_4745_,
                                v_a_4747_,
                                v___y_4735_,
                                v___y_4736_,
                                v___y_4737_,
                                v___y_4738_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4748_) == 0 {
                                v_a_4749_ = crate::leanh::lean_ctor_get(v___x_4748_, 0);
                                crate::leanh::lean_inc_n(v_a_4749_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_4748_, 1);
                                v___x_4750_ = l_Lean_mkAppN(v_a_4749_, v_mvars_4742_);
                                crate::leanh::lean_dec_ref(v_mvars_4742_);
                                v___x_4751_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_4734_, v___x_4750_, v___y_4736_);
                                v_isSharedCheck_4759_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4751_)) as u8;
                                if v_isSharedCheck_4759_ == 0 {
                                    v_unused_4760_ = crate::leanh::lean_ctor_get(v___x_4751_, 0);
                                    crate::leanh::lean_dec(v_unused_4760_);
                                    v___x_4753_ = v___x_4751_;
                                    v_isShared_4754_ = v_isSharedCheck_4759_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4751_);
                                    v___x_4753_ = crate::leanh::lean_box(0);
                                    v_isShared_4754_ = v_isSharedCheck_4759_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_mvars_4742_);
                                crate::leanh::lean_dec(v_mvarId_4734_);
                                v_a_4761_ = crate::leanh::lean_ctor_get(v___x_4748_, 0);
                                v_isSharedCheck_4768_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4748_)) as u8;
                                if v_isSharedCheck_4768_ == 0 {
                                    v___x_4763_ = v___x_4748_;
                                    v_isShared_4764_ = v_isSharedCheck_4768_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4761_);
                                    crate::leanh::lean_dec(v___x_4748_);
                                    v___x_4763_ = crate::leanh::lean_box(0);
                                    v_isShared_4764_ = v_isSharedCheck_4768_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4745_);
                            crate::leanh::lean_dec_ref(v_mvars_4742_);
                            crate::leanh::lean_dec(v_mvarId_4734_);
                            v_a_4769_ = crate::leanh::lean_ctor_get(v___x_4746_, 0);
                            v_isSharedCheck_4776_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4746_)) as u8;
                            if v_isSharedCheck_4776_ == 0 {
                                v___x_4771_ = v___x_4746_;
                                v_isShared_4772_ = v_isSharedCheck_4776_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4769_);
                                crate::leanh::lean_dec(v___x_4746_);
                                v___x_4771_ = crate::leanh::lean_box(0);
                                v_isShared_4772_ = v_isSharedCheck_4776_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mvars_4742_);
                        crate::leanh::lean_dec(v_mvarId_4734_);
                        v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4744_, 0);
                        v_isSharedCheck_4784_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4744_)) as u8;
                        if v_isSharedCheck_4784_ == 0 {
                            v___x_4779_ = v___x_4744_;
                            v_isShared_4780_ = v_isSharedCheck_4784_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4777_);
                            crate::leanh::lean_dec(v___x_4744_);
                            v___x_4779_ = crate::leanh::lean_box(0);
                            v_isShared_4780_ = v_isSharedCheck_4784_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4734_);
                    crate::leanh::lean_dec_ref(v___f_4733_);
                    v_a_4785_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4792_ = (!crate::leanh::lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4792_ == 0 {
                        v___x_4787_ = v___x_4740_;
                        v_isShared_4788_ = v_isSharedCheck_4792_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4785_);
                        crate::leanh::lean_dec(v___x_4740_);
                        v___x_4787_ = crate::leanh::lean_box(0);
                        v_isShared_4788_ = v_isSharedCheck_4792_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4755_ = l_Lean_Expr_mvarId_x21(v_a_4749_);
                crate::leanh::lean_dec(v_a_4749_);
                if v_isShared_4754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4753_, 0, v___x_4755_);
                    v___x_4757_ = v___x_4753_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
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
                    v_reuseFailAlloc_4767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
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
                    v_reuseFailAlloc_4775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4769_);
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
                    v_reuseFailAlloc_4783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
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
                    v_reuseFailAlloc_4791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
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
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v___x_4794_: *mut crate::leanh::LeanObject,
    mut v___f_4795_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1977__boxed_4802_: u8 = 0;
    let mut v_res_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977__boxed_4802_ = (crate::leanh::lean_unbox(v___x_4794_) as u8);
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
    crate::leanh::lean_dec(v___y_4800_);
    crate::leanh::lean_dec_ref(v___y_4799_);
    crate::leanh::lean_dec(v___y_4798_);
    crate::leanh::lean_dec_ref(v___y_4797_);
    return v_res_4803_;
}
pub unsafe fn l_Lean_MVarId_abstractMVars(
    mut v_mvarId_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
    mut v_a_4807_: *mut crate::leanh::LeanObject,
    mut v_a_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v___x_4819_: u8 = 0;
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4830_: u8 = 0;
    let mut v_a_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4834_: u8 = 0;
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_a_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4810_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                crate::leanh::lean_inc(v_mvarId_4804_);
                v___x_4811_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4804_,
                    v___x_4810_,
                    v_a_4805_,
                    v_a_4806_,
                    v_a_4807_,
                    v_a_4808_,
                );
                if crate::leanh::lean_obj_tag(v___x_4811_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4811_, 1);
                    crate::leanh::lean_inc(v_mvarId_4804_);
                    v___x_4812_ = l_Lean_MVarId_getType(
                        v_mvarId_4804_,
                        v_a_4805_,
                        v_a_4806_,
                        v_a_4807_,
                        v_a_4808_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4812_) == 0 {
                        v_a_4813_ = crate::leanh::lean_ctor_get(v___x_4812_, 0);
                        crate::leanh::lean_inc(v_a_4813_);
                        crate::leanh::lean_dec_ref_known(v___x_4812_, 1);
                        v___x_4814_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_4813_, v_a_4806_);
                        v_a_4815_ = crate::leanh::lean_ctor_get(v___x_4814_, 0);
                        v_isSharedCheck_4830_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4814_)) as u8;
                        if v_isSharedCheck_4830_ == 0 {
                            v___x_4817_ = v___x_4814_;
                            v_isShared_4818_ = v_isSharedCheck_4830_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4815_);
                            crate::leanh::lean_dec(v___x_4814_);
                            v___x_4817_ = crate::leanh::lean_box(0);
                            v_isShared_4818_ = v_isSharedCheck_4830_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_4804_);
                        v_a_4831_ = crate::leanh::lean_ctor_get(v___x_4812_, 0);
                        v_isSharedCheck_4838_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4812_)) as u8;
                        if v_isSharedCheck_4838_ == 0 {
                            v___x_4833_ = v___x_4812_;
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4831_);
                            crate::leanh::lean_dec(v___x_4812_);
                            v___x_4833_ = crate::leanh::lean_box(0);
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4804_);
                    v_a_4839_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
                    v_isSharedCheck_4846_ = (!crate::leanh::lean_is_exclusive(v___x_4811_)) as u8;
                    if v_isSharedCheck_4846_ == 0 {
                        v___x_4841_ = v___x_4811_;
                        v_isShared_4842_ = v_isSharedCheck_4846_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4839_);
                        crate::leanh::lean_dec(v___x_4811_);
                        v___x_4841_ = crate::leanh::lean_box(0);
                        v_isShared_4842_ = v_isSharedCheck_4846_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4819_ = l_Lean_Expr_hasExprMVar(v_a_4815_);
                if v___x_4819_ == 0 {
                    crate::leanh::lean_dec(v_a_4815_);
                    if v_isShared_4818_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4817_, 0, v_mvarId_4804_);
                        v___x_4821_ = v___x_4817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_mvarId_4804_);
                        v___x_4821_ = v_reuseFailAlloc_4822_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4817_);
                    v___x_4823_ = 0;
                    v___x_4824_ = crate::leanh::lean_box((v___x_4823_) as usize);
                    v___x_4825_ = crate::leanh::lean_box((v___x_4819_) as usize);
                    v___f_4826_ = crate::leanh::lean_alloc_closure(
                        l_Lean_MVarId_abstractMVars___lam__0___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_4826_, 0, v___x_4824_);
                    crate::leanh::lean_closure_set(v___f_4826_, 1, v___x_4825_);
                    v___x_4827_ = crate::leanh::lean_box((v___x_4823_) as usize);
                    crate::leanh::lean_inc(v_mvarId_4804_);
                    v___f_4828_ = crate::leanh::lean_alloc_closure(
                        l_Lean_MVarId_abstractMVars___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_4828_, 0, v_a_4815_);
                    crate::leanh::lean_closure_set(v___f_4828_, 1, v___x_4827_);
                    crate::leanh::lean_closure_set(v___f_4828_, 2, v___f_4826_);
                    crate::leanh::lean_closure_set(v___f_4828_, 3, v_mvarId_4804_);
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
                    v_reuseFailAlloc_4837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
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
                    v_reuseFailAlloc_4845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
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
    mut v_mvarId_4847_: *mut crate::leanh::LeanObject,
    mut v_a_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4853_ =
        l_Lean_MVarId_abstractMVars(v_mvarId_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
    crate::leanh::lean_dec(v_a_4851_);
    crate::leanh::lean_dec_ref(v_a_4850_);
    crate::leanh::lean_dec(v_a_4849_);
    crate::leanh::lean_dec_ref(v_a_4848_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_MVarId_transformTarget___lam__0(
    mut v_mvarId_4854_: *mut crate::leanh::LeanObject,
    mut v___x_4855_: *mut crate::leanh::LeanObject,
    mut v_f_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_unused_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4888_: u8 = 0;
    let mut v_a_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4892_: u8 = 0;
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut v_a_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_a_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v_a_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4854_);
                v___x_4862_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4854_,
                    v___x_4855_,
                    v___y_4857_,
                    v___y_4858_,
                    v___y_4859_,
                    v___y_4860_,
                );
                if crate::leanh::lean_obj_tag(v___x_4862_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4862_, 1);
                    crate::leanh::lean_inc(v_mvarId_4854_);
                    v___x_4863_ = l_Lean_MVarId_getTag(
                        v_mvarId_4854_,
                        v___y_4857_,
                        v___y_4858_,
                        v___y_4859_,
                        v___y_4860_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4863_) == 0 {
                        v_a_4864_ = crate::leanh::lean_ctor_get(v___x_4863_, 0);
                        crate::leanh::lean_inc(v_a_4864_);
                        crate::leanh::lean_dec_ref_known(v___x_4863_, 1);
                        crate::leanh::lean_inc(v_mvarId_4854_);
                        v___x_4865_ = l_Lean_MVarId_getType(
                            v_mvarId_4854_,
                            v___y_4857_,
                            v___y_4858_,
                            v___y_4859_,
                            v___y_4860_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4865_) == 0 {
                            v_a_4866_ = crate::leanh::lean_ctor_get(v___x_4865_, 0);
                            crate::leanh::lean_inc(v_a_4866_);
                            crate::leanh::lean_dec_ref_known(v___x_4865_, 1);
                            crate::leanh::lean_inc(v___y_4860_);
                            crate::leanh::lean_inc_ref(v___y_4859_);
                            crate::leanh::lean_inc(v___y_4858_);
                            crate::leanh::lean_inc_ref(v___y_4857_);
                            v___x_4867_ = crate::leanh::lean_apply_6(
                                v_f_4856_,
                                v_a_4866_,
                                v___y_4857_,
                                v___y_4858_,
                                v___y_4859_,
                                v___y_4860_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4867_) == 0 {
                                v_a_4868_ = crate::leanh::lean_ctor_get(v___x_4867_, 0);
                                crate::leanh::lean_inc(v_a_4868_);
                                crate::leanh::lean_dec_ref_known(v___x_4867_, 1);
                                v___x_4869_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v_a_4868_,
                                    v_a_4864_,
                                    v___y_4857_,
                                    v___y_4858_,
                                    v___y_4859_,
                                    v___y_4860_,
                                );
                                crate::leanh::lean_dec(v___y_4860_);
                                crate::leanh::lean_dec_ref(v___y_4859_);
                                crate::leanh::lean_dec_ref(v___y_4857_);
                                if crate::leanh::lean_obj_tag(v___x_4869_) == 0 {
                                    v_a_4870_ = crate::leanh::lean_ctor_get(v___x_4869_, 0);
                                    crate::leanh::lean_inc_n(v_a_4870_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_4869_, 1);
                                    v___x_4871_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_4854_, v_a_4870_, v___y_4858_);
                                    crate::leanh::lean_dec(v___y_4858_);
                                    v_isSharedCheck_4879_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4871_)) as u8;
                                    if v_isSharedCheck_4879_ == 0 {
                                        v_unused_4880_ =
                                            crate::leanh::lean_ctor_get(v___x_4871_, 0);
                                        crate::leanh::lean_dec(v_unused_4880_);
                                        v___x_4873_ = v___x_4871_;
                                        v_isShared_4874_ = v_isSharedCheck_4879_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4871_);
                                        v___x_4873_ = crate::leanh::lean_box(0);
                                        v_isShared_4874_ = v_isSharedCheck_4879_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___y_4858_);
                                    crate::leanh::lean_dec(v_mvarId_4854_);
                                    v_a_4881_ = crate::leanh::lean_ctor_get(v___x_4869_, 0);
                                    v_isSharedCheck_4888_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4869_)) as u8;
                                    if v_isSharedCheck_4888_ == 0 {
                                        v___x_4883_ = v___x_4869_;
                                        v_isShared_4884_ = v_isSharedCheck_4888_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4881_);
                                        crate::leanh::lean_dec(v___x_4869_);
                                        v___x_4883_ = crate::leanh::lean_box(0);
                                        v_isShared_4884_ = v_isSharedCheck_4888_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4864_);
                                crate::leanh::lean_dec(v___y_4860_);
                                crate::leanh::lean_dec_ref(v___y_4859_);
                                crate::leanh::lean_dec(v___y_4858_);
                                crate::leanh::lean_dec_ref(v___y_4857_);
                                crate::leanh::lean_dec(v_mvarId_4854_);
                                v_a_4889_ = crate::leanh::lean_ctor_get(v___x_4867_, 0);
                                v_isSharedCheck_4896_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4867_)) as u8;
                                if v_isSharedCheck_4896_ == 0 {
                                    v___x_4891_ = v___x_4867_;
                                    v_isShared_4892_ = v_isSharedCheck_4896_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4889_);
                                    crate::leanh::lean_dec(v___x_4867_);
                                    v___x_4891_ = crate::leanh::lean_box(0);
                                    v_isShared_4892_ = v_isSharedCheck_4896_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4864_);
                            crate::leanh::lean_dec(v___y_4860_);
                            crate::leanh::lean_dec_ref(v___y_4859_);
                            crate::leanh::lean_dec(v___y_4858_);
                            crate::leanh::lean_dec_ref(v___y_4857_);
                            crate::leanh::lean_dec_ref(v_f_4856_);
                            crate::leanh::lean_dec(v_mvarId_4854_);
                            v_a_4897_ = crate::leanh::lean_ctor_get(v___x_4865_, 0);
                            v_isSharedCheck_4904_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4865_)) as u8;
                            if v_isSharedCheck_4904_ == 0 {
                                v___x_4899_ = v___x_4865_;
                                v_isShared_4900_ = v_isSharedCheck_4904_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4897_);
                                crate::leanh::lean_dec(v___x_4865_);
                                v___x_4899_ = crate::leanh::lean_box(0);
                                v_isShared_4900_ = v_isSharedCheck_4904_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_4860_);
                        crate::leanh::lean_dec_ref(v___y_4859_);
                        crate::leanh::lean_dec(v___y_4858_);
                        crate::leanh::lean_dec_ref(v___y_4857_);
                        crate::leanh::lean_dec_ref(v_f_4856_);
                        crate::leanh::lean_dec(v_mvarId_4854_);
                        v_a_4905_ = crate::leanh::lean_ctor_get(v___x_4863_, 0);
                        v_isSharedCheck_4912_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4863_)) as u8;
                        if v_isSharedCheck_4912_ == 0 {
                            v___x_4907_ = v___x_4863_;
                            v_isShared_4908_ = v_isSharedCheck_4912_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4905_);
                            crate::leanh::lean_dec(v___x_4863_);
                            v___x_4907_ = crate::leanh::lean_box(0);
                            v_isShared_4908_ = v_isSharedCheck_4912_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4860_);
                    crate::leanh::lean_dec_ref(v___y_4859_);
                    crate::leanh::lean_dec(v___y_4858_);
                    crate::leanh::lean_dec_ref(v___y_4857_);
                    crate::leanh::lean_dec_ref(v_f_4856_);
                    crate::leanh::lean_dec(v_mvarId_4854_);
                    v_a_4913_ = crate::leanh::lean_ctor_get(v___x_4862_, 0);
                    v_isSharedCheck_4920_ = (!crate::leanh::lean_is_exclusive(v___x_4862_)) as u8;
                    if v_isSharedCheck_4920_ == 0 {
                        v___x_4915_ = v___x_4862_;
                        v_isShared_4916_ = v_isSharedCheck_4920_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4913_);
                        crate::leanh::lean_dec(v___x_4862_);
                        v___x_4915_ = crate::leanh::lean_box(0);
                        v_isShared_4916_ = v_isSharedCheck_4920_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4875_ = l_Lean_Expr_mvarId_x21(v_a_4870_);
                crate::leanh::lean_dec(v_a_4870_);
                if v_isShared_4874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4873_, 0, v___x_4875_);
                    v___x_4877_ = v___x_4873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
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
                    v_reuseFailAlloc_4887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
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
                    v_reuseFailAlloc_4895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
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
                    v_reuseFailAlloc_4903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
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
                    v_reuseFailAlloc_4911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
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
                    v_reuseFailAlloc_4919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
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
    mut v_mvarId_4921_: *mut crate::leanh::LeanObject,
    mut v___x_4922_: *mut crate::leanh::LeanObject,
    mut v_f_4923_: *mut crate::leanh::LeanObject,
    mut v___y_4924_: *mut crate::leanh::LeanObject,
    mut v___y_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_4930_: *mut crate::leanh::LeanObject,
    mut v_f_4931_: *mut crate::leanh::LeanObject,
    mut v_a_4932_: *mut crate::leanh::LeanObject,
    mut v_a_4933_: *mut crate::leanh::LeanObject,
    mut v_a_4934_: *mut crate::leanh::LeanObject,
    mut v_a_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4937_ = l_Lean_MVarId_ensureNoMVar___closed__1;
    crate::leanh::lean_inc(v_mvarId_4930_);
    v___f_4938_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_transformTarget___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4938_, 0, v_mvarId_4930_);
    crate::leanh::lean_closure_set(v___f_4938_, 1, v___x_4937_);
    crate::leanh::lean_closure_set(v___f_4938_, 2, v_f_4931_);
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
    mut v_mvarId_4940_: *mut crate::leanh::LeanObject,
    mut v_f_4941_: *mut crate::leanh::LeanObject,
    mut v_a_4942_: *mut crate::leanh::LeanObject,
    mut v_a_4943_: *mut crate::leanh::LeanObject,
    mut v_a_4944_: *mut crate::leanh::LeanObject,
    mut v_a_4945_: *mut crate::leanh::LeanObject,
    mut v_a_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4947_ = l_Lean_MVarId_transformTarget(
        v_mvarId_4940_,
        v_f_4941_,
        v_a_4942_,
        v_a_4943_,
        v_a_4944_,
        v_a_4945_,
    );
    crate::leanh::lean_dec(v_a_4945_);
    crate::leanh::lean_dec_ref(v_a_4944_);
    crate::leanh::lean_dec(v_a_4943_);
    crate::leanh::lean_dec_ref(v_a_4942_);
    return v_res_4947_;
}
pub unsafe fn l_Lean_MVarId_unfoldReducible(
    mut v_mvarId_4949_: *mut crate::leanh::LeanObject,
    mut v_a_4950_: *mut crate::leanh::LeanObject,
    mut v_a_4951_: *mut crate::leanh::LeanObject,
    mut v_a_4952_: *mut crate::leanh::LeanObject,
    mut v_a_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_4957_: *mut crate::leanh::LeanObject,
    mut v_a_4958_: *mut crate::leanh::LeanObject,
    mut v_a_4959_: *mut crate::leanh::LeanObject,
    mut v_a_4960_: *mut crate::leanh::LeanObject,
    mut v_a_4961_: *mut crate::leanh::LeanObject,
    mut v_a_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4963_ =
        l_Lean_MVarId_unfoldReducible(v_mvarId_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_);
    crate::leanh::lean_dec(v_a_4961_);
    crate::leanh::lean_dec_ref(v_a_4960_);
    crate::leanh::lean_dec(v_a_4959_);
    crate::leanh::lean_dec_ref(v_a_4958_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_MVarId_betaReduce___lam__0(
    mut v_x_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
    mut v___y_4967_: *mut crate::leanh::LeanObject,
    mut v___y_4968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4970_ = l_Lean_Core_betaReduce(v_x_4964_, v___y_4967_, v___y_4968_);
    return v___x_4970_;
}
pub unsafe fn l_Lean_MVarId_betaReduce___lam__0___boxed(
    mut v_x_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Lean_MVarId_betaReduce___lam__0(
        v_x_4971_,
        v___y_4972_,
        v___y_4973_,
        v___y_4974_,
        v___y_4975_,
    );
    crate::leanh::lean_dec(v___y_4975_);
    crate::leanh::lean_dec_ref(v___y_4974_);
    crate::leanh::lean_dec(v___y_4973_);
    crate::leanh::lean_dec_ref(v___y_4972_);
    return v_res_4977_;
}
pub unsafe fn l_Lean_MVarId_betaReduce(
    mut v_mvarId_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
    mut v_a_4981_: *mut crate::leanh::LeanObject,
    mut v_a_4982_: *mut crate::leanh::LeanObject,
    mut v_a_4983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_4987_: *mut crate::leanh::LeanObject,
    mut v_a_4988_: *mut crate::leanh::LeanObject,
    mut v_a_4989_: *mut crate::leanh::LeanObject,
    mut v_a_4990_: *mut crate::leanh::LeanObject,
    mut v_a_4991_: *mut crate::leanh::LeanObject,
    mut v_a_4992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4993_ =
        l_Lean_MVarId_betaReduce(v_mvarId_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
    crate::leanh::lean_dec(v_a_4991_);
    crate::leanh::lean_dec_ref(v_a_4990_);
    crate::leanh::lean_dec(v_a_4989_);
    crate::leanh::lean_dec_ref(v_a_4988_);
    return v_res_4993_;
}
pub unsafe fn _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4997_ = crate::leanh::lean_box(0);
    v___x_4998_ = l_Lean_MVarId_byContra_x3f___lam__0___closed__1;
    v___x_4999_ = l_Lean_mkConst(v___x_4998_, v___x_4997_);
    return v___x_4999_;
}
pub unsafe fn _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5005_ = crate::leanh::lean_box(0);
    v___x_5006_ = l_Lean_MVarId_byContra_x3f___lam__0___closed__5;
    v___x_5007_ = l_Lean_mkConst(v___x_5006_, v___x_5005_);
    return v___x_5007_;
}
pub unsafe fn l_Lean_MVarId_byContra_x3f___lam__0(
    mut v_mvarId_5008_: *mut crate::leanh::LeanObject,
    mut v___x_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
    mut v___y_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: u8 = 0;
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5035_: u8 = 0;
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5041_: u8 = 0;
    let mut v_unused_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5046_: u8 = 0;
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5050_: u8 = 0;
    let mut v_a_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5054_: u8 = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5058_: u8 = 0;
    let mut v_a_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5062_: u8 = 0;
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5066_: u8 = 0;
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_a_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut v_a_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_5008_);
                v___x_5015_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5008_,
                    v___x_5009_,
                    v___y_5010_,
                    v___y_5011_,
                    v___y_5012_,
                    v___y_5013_,
                );
                if crate::leanh::lean_obj_tag(v___x_5015_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5015_, 1);
                    crate::leanh::lean_inc(v_mvarId_5008_);
                    v___x_5016_ = l_Lean_MVarId_getType(
                        v_mvarId_5008_,
                        v___y_5010_,
                        v___y_5011_,
                        v___y_5012_,
                        v___y_5013_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5016_) == 0 {
                        v_a_5017_ = crate::leanh::lean_ctor_get(v___x_5016_, 0);
                        v_isSharedCheck_5071_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5016_)) as u8;
                        if v_isSharedCheck_5071_ == 0 {
                            v___x_5019_ = v___x_5016_;
                            v_isShared_5020_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5017_);
                            crate::leanh::lean_dec(v___x_5016_);
                            v___x_5019_ = crate::leanh::lean_box(0);
                            v_isShared_5020_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_5008_);
                        v_a_5072_ = crate::leanh::lean_ctor_get(v___x_5016_, 0);
                        v_isSharedCheck_5079_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5016_)) as u8;
                        if v_isSharedCheck_5079_ == 0 {
                            v___x_5074_ = v___x_5016_;
                            v_isShared_5075_ = v_isSharedCheck_5079_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5072_);
                            crate::leanh::lean_dec(v___x_5016_);
                            v___x_5074_ = crate::leanh::lean_box(0);
                            v_isShared_5075_ = v_isSharedCheck_5079_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_5008_);
                    v_a_5080_ = crate::leanh::lean_ctor_get(v___x_5015_, 0);
                    v_isSharedCheck_5087_ = (!crate::leanh::lean_is_exclusive(v___x_5015_)) as u8;
                    if v_isSharedCheck_5087_ == 0 {
                        v___x_5082_ = v___x_5015_;
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5080_);
                        crate::leanh::lean_dec(v___x_5015_);
                        v___x_5082_ = crate::leanh::lean_box(0);
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_5017_);
                v___x_5021_ = l_Lean_Expr_isFalse(v_a_5017_);
                if v___x_5021_ == 0 {
                    crate::leanh::lean_del_object(v___x_5019_);
                    crate::leanh::lean_inc(v_a_5017_);
                    v___x_5022_ = l_Lean_mkNot(v_a_5017_);
                    v___x_5023_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_byContra_x3f___lam__0___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once
                        ),
                        _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2,
                    );
                    v___x_5024_ =
                        l_Lean_mkArrow(v___x_5022_, v___x_5023_, v___y_5012_, v___y_5013_);
                    if crate::leanh::lean_obj_tag(v___x_5024_) == 0 {
                        v_a_5025_ = crate::leanh::lean_ctor_get(v___x_5024_, 0);
                        crate::leanh::lean_inc(v_a_5025_);
                        crate::leanh::lean_dec_ref_known(v___x_5024_, 1);
                        crate::leanh::lean_inc(v_mvarId_5008_);
                        v___x_5026_ = l_Lean_MVarId_getTag(
                            v_mvarId_5008_,
                            v___y_5010_,
                            v___y_5011_,
                            v___y_5012_,
                            v___y_5013_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5026_) == 0 {
                            v_a_5027_ = crate::leanh::lean_ctor_get(v___x_5026_, 0);
                            crate::leanh::lean_inc(v_a_5027_);
                            crate::leanh::lean_dec_ref_known(v___x_5026_, 1);
                            v___x_5028_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_5025_,
                                v_a_5027_,
                                v___y_5010_,
                                v___y_5011_,
                                v___y_5012_,
                                v___y_5013_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5028_) == 0 {
                                v_a_5029_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                                crate::leanh::lean_inc_n(v_a_5029_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_5028_, 1);
                                v___x_5030_ = crate::leanh::lean_obj_once(
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
                                    (!crate::leanh::lean_is_exclusive(v___x_5032_)) as u8;
                                if v_isSharedCheck_5041_ == 0 {
                                    v_unused_5042_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                                    crate::leanh::lean_dec(v_unused_5042_);
                                    v___x_5034_ = v___x_5032_;
                                    v_isShared_5035_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_5032_);
                                    v___x_5034_ = crate::leanh::lean_box(0);
                                    v_isShared_5035_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5017_);
                                crate::leanh::lean_dec(v_mvarId_5008_);
                                v_a_5043_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                                v_isSharedCheck_5050_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5028_)) as u8;
                                if v_isSharedCheck_5050_ == 0 {
                                    v___x_5045_ = v___x_5028_;
                                    v_isShared_5046_ = v_isSharedCheck_5050_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5043_);
                                    crate::leanh::lean_dec(v___x_5028_);
                                    v___x_5045_ = crate::leanh::lean_box(0);
                                    v_isShared_5046_ = v_isSharedCheck_5050_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5025_);
                            crate::leanh::lean_dec(v_a_5017_);
                            crate::leanh::lean_dec(v_mvarId_5008_);
                            v_a_5051_ = crate::leanh::lean_ctor_get(v___x_5026_, 0);
                            v_isSharedCheck_5058_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5026_)) as u8;
                            if v_isSharedCheck_5058_ == 0 {
                                v___x_5053_ = v___x_5026_;
                                v_isShared_5054_ = v_isSharedCheck_5058_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5051_);
                                crate::leanh::lean_dec(v___x_5026_);
                                v___x_5053_ = crate::leanh::lean_box(0);
                                v_isShared_5054_ = v_isSharedCheck_5058_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5017_);
                        crate::leanh::lean_dec(v_mvarId_5008_);
                        v_a_5059_ = crate::leanh::lean_ctor_get(v___x_5024_, 0);
                        v_isSharedCheck_5066_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5024_)) as u8;
                        if v_isSharedCheck_5066_ == 0 {
                            v___x_5061_ = v___x_5024_;
                            v_isShared_5062_ = v_isSharedCheck_5066_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5059_);
                            crate::leanh::lean_dec(v___x_5024_);
                            v___x_5061_ = crate::leanh::lean_box(0);
                            v_isShared_5062_ = v_isSharedCheck_5066_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5017_);
                    crate::leanh::lean_dec(v_mvarId_5008_);
                    v___x_5067_ = crate::leanh::lean_box(0);
                    if v_isShared_5020_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5019_, 0, v___x_5067_);
                        v___x_5069_ = v___x_5019_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
                        v___x_5069_ = v_reuseFailAlloc_5070_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5036_ = l_Lean_Expr_mvarId_x21(v_a_5029_);
                crate::leanh::lean_dec(v_a_5029_);
                v___x_5037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5037_, 0, v___x_5036_);
                if v_isShared_5035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5034_, 0, v___x_5037_);
                    v___x_5039_ = v___x_5034_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
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
                    v_reuseFailAlloc_5049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
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
                    v_reuseFailAlloc_5057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5057_, 0, v_a_5051_);
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
                    v_reuseFailAlloc_5065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_a_5059_);
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
                    v_reuseFailAlloc_5078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
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
                    v_reuseFailAlloc_5086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
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
    mut v_mvarId_5088_: *mut crate::leanh::LeanObject,
    mut v___x_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5095_ = l_Lean_MVarId_byContra_x3f___lam__0(
        v_mvarId_5088_,
        v___x_5089_,
        v___y_5090_,
        v___y_5091_,
        v___y_5092_,
        v___y_5093_,
    );
    crate::leanh::lean_dec(v___y_5093_);
    crate::leanh::lean_dec_ref(v___y_5092_);
    crate::leanh::lean_dec(v___y_5091_);
    crate::leanh::lean_dec_ref(v___y_5090_);
    return v_res_5095_;
}
pub unsafe fn l_Lean_MVarId_byContra_x3f(
    mut v_mvarId_5100_: *mut crate::leanh::LeanObject,
    mut v_a_5101_: *mut crate::leanh::LeanObject,
    mut v_a_5102_: *mut crate::leanh::LeanObject,
    mut v_a_5103_: *mut crate::leanh::LeanObject,
    mut v_a_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Lean_MVarId_byContra_x3f___closed__1;
    crate::leanh::lean_inc(v_mvarId_5100_);
    v___f_5107_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_byContra_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5107_, 0, v_mvarId_5100_);
    crate::leanh::lean_closure_set(v___f_5107_, 1, v___x_5106_);
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
    mut v_mvarId_5109_: *mut crate::leanh::LeanObject,
    mut v_a_5110_: *mut crate::leanh::LeanObject,
    mut v_a_5111_: *mut crate::leanh::LeanObject,
    mut v_a_5112_: *mut crate::leanh::LeanObject,
    mut v_a_5113_: *mut crate::leanh::LeanObject,
    mut v_a_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5115_ =
        l_Lean_MVarId_byContra_x3f(v_mvarId_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_);
    crate::leanh::lean_dec(v_a_5113_);
    crate::leanh::lean_dec_ref(v_a_5112_);
    crate::leanh::lean_dec(v_a_5111_);
    crate::leanh::lean_dec_ref(v_a_5110_);
    return v_res_5115_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5117_ =
        l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0;
    v___x_5118_ = l_Lean_stringToMessageData(v___x_5117_);
    return v___x_5118_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5120_ =
        l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2;
    v___x_5121_ = l_Lean_stringToMessageData(v___x_5120_);
    return v___x_5121_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5123_ =
        l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4;
    v___x_5124_ = l_Lean_stringToMessageData(v___x_5123_);
    return v___x_5124_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(
    mut v_as_x27_5125_: *mut crate::leanh::LeanObject,
    mut v_b_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5140_: u8 = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5169_: u8 = 0;
    let mut v_reuseFailAlloc_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5174_: u8 = 0;
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v_isSharedCheck_5179_: u8 = 0;
    let mut v_unused_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: u8 = 0;
    let mut v___x_5182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5125_) == 0 {
                    v___x_5132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5132_, 0, v_b_5126_);
                    return v___x_5132_;
                } else {
                    v_head_5133_ = crate::leanh::lean_ctor_get(v_as_x27_5125_, 0);
                    v_tail_5134_ = crate::leanh::lean_ctor_get(v_as_x27_5125_, 1);
                    crate::leanh::lean_inc(v_head_5133_);
                    crate::leanh::lean_inc(v_b_5126_);
                    v___x_5135_ = l_Lean_MVarId_clear(
                        v_b_5126_,
                        v_head_5133_,
                        v___y_5127_,
                        v___y_5128_,
                        v___y_5129_,
                        v___y_5130_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5135_) == 0 {
                        crate::leanh::lean_dec(v_b_5126_);
                        v_a_5136_ = crate::leanh::lean_ctor_get(v___x_5135_, 0);
                        crate::leanh::lean_inc(v_a_5136_);
                        crate::leanh::lean_dec_ref_known(v___x_5135_, 1);
                        v_as_x27_5125_ = v_tail_5134_;
                        v_b_5126_ = v_a_5136_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5138_ = crate::leanh::lean_ctor_get(v___x_5135_, 0);
                        crate::leanh::lean_inc(v_a_5138_);
                        v___x_5181_ = l_Lean_Exception_isInterrupt(v_a_5138_);
                        if v___x_5181_ == 0 {
                            v___x_5182_ = l_Lean_Exception_isRuntime(v_a_5138_);
                            v___y_5140_ = v___x_5182_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_5138_);
                            v___y_5140_ = v___x_5181_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_5140_ == 0 {
                    v_isSharedCheck_5179_ = (!crate::leanh::lean_is_exclusive(v___x_5135_)) as u8;
                    if v_isSharedCheck_5179_ == 0 {
                        v_unused_5180_ = crate::leanh::lean_ctor_get(v___x_5135_, 0);
                        crate::leanh::lean_dec(v_unused_5180_);
                        v___x_5142_ = v___x_5135_;
                        v_isShared_5143_ = v_isSharedCheck_5179_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5135_);
                        v___x_5142_ = crate::leanh::lean_box(0);
                        v_isShared_5143_ = v_isSharedCheck_5179_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5126_);
                    return v___x_5135_;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_head_5133_);
                v___x_5144_ = l_Lean_FVarId_getDecl___redArg(
                    v_head_5133_,
                    v___y_5127_,
                    v___y_5129_,
                    v___y_5130_,
                );
                if crate::leanh::lean_obj_tag(v___x_5144_) == 0 {
                    v_a_5145_ = crate::leanh::lean_ctor_get(v___x_5144_, 0);
                    crate::leanh::lean_inc(v_a_5145_);
                    crate::leanh::lean_dec_ref_known(v___x_5144_, 1);
                    v___x_5146_ = l_Lean_LocalDecl_isAuxDecl(v_a_5145_);
                    if v___x_5146_ == 0 {
                        crate::leanh::lean_dec(v_a_5145_);
                        crate::leanh::lean_del_object(v___x_5142_);
                        v_as_x27_5125_ = v_tail_5134_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5148_ = l_Lean_LocalDecl_userName(v_a_5145_);
                        crate::leanh::lean_dec(v_a_5145_);
                        v___x_5149_ = l_Lean_MVarId_ensureNoMVar___closed__1;
                        v___x_5150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
                        v___x_5151_ = l_Lean_MessageData_ofName(v___x_5148_);
                        crate::leanh::lean_inc_ref(v___x_5151_);
                        v___x_5152_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5150_);
                        crate::leanh::lean_ctor_set(v___x_5152_, 1, v___x_5151_);
                        v___x_5153_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
                        v___x_5154_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5154_, 0, v___x_5152_);
                        crate::leanh::lean_ctor_set(v___x_5154_, 1, v___x_5153_);
                        v___x_5155_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5155_, 0, v___x_5154_);
                        crate::leanh::lean_ctor_set(v___x_5155_, 1, v___x_5151_);
                        v___x_5156_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
                        v___x_5157_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5157_, 0, v___x_5155_);
                        crate::leanh::lean_ctor_set(v___x_5157_, 1, v___x_5156_);
                        if v_isShared_5143_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5142_, 0, v___x_5157_);
                            v___x_5159_ = v___x_5142_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5170_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5157_);
                            v___x_5159_ = v_reuseFailAlloc_5170_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5142_);
                    crate::leanh::lean_dec(v_b_5126_);
                    v_a_5171_ = crate::leanh::lean_ctor_get(v___x_5144_, 0);
                    v_isSharedCheck_5178_ = (!crate::leanh::lean_is_exclusive(v___x_5144_)) as u8;
                    if v_isSharedCheck_5178_ == 0 {
                        v___x_5173_ = v___x_5144_;
                        v_isShared_5174_ = v_isSharedCheck_5178_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5171_);
                        crate::leanh::lean_dec(v___x_5144_);
                        v___x_5173_ = crate::leanh::lean_box(0);
                        v_isShared_5174_ = v_isSharedCheck_5178_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_b_5126_);
                v___x_5160_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5149_,
                    v_b_5126_,
                    v___x_5159_,
                    v___y_5127_,
                    v___y_5128_,
                    v___y_5129_,
                    v___y_5130_,
                );
                if crate::leanh::lean_obj_tag(v___x_5160_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5160_, 1);
                    v_as_x27_5125_ = v_tail_5134_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_b_5126_);
                    v_a_5162_ = crate::leanh::lean_ctor_get(v___x_5160_, 0);
                    v_isSharedCheck_5169_ = (!crate::leanh::lean_is_exclusive(v___x_5160_)) as u8;
                    if v_isSharedCheck_5169_ == 0 {
                        v___x_5164_ = v___x_5160_;
                        v_isShared_5165_ = v_isSharedCheck_5169_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5162_);
                        crate::leanh::lean_dec(v___x_5160_);
                        v___x_5164_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
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
                    v_reuseFailAlloc_5177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
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
    mut v_as_x27_5183_: *mut crate::leanh::LeanObject,
    mut v_b_5184_: *mut crate::leanh::LeanObject,
    mut v___y_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5190_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(
        v_as_x27_5183_,
        v_b_5184_,
        v___y_5185_,
        v___y_5186_,
        v___y_5187_,
        v___y_5188_,
    );
    crate::leanh::lean_dec(v___y_5188_);
    crate::leanh::lean_dec_ref(v___y_5187_);
    crate::leanh::lean_dec(v___y_5186_);
    crate::leanh::lean_dec_ref(v___y_5185_);
    crate::leanh::lean_dec(v_as_x27_5183_);
    return v_res_5190_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_as_5191_: *mut crate::leanh::LeanObject,
    mut v_sz_5192_: usize,
    mut v_i_5193_: usize,
    mut v_b_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v_reuseFailAlloc_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut v_unused_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5196_ = lean_usize_dec_lt(v_i_5193_, v_sz_5192_);
                if v___x_5196_ == 0 {
                    v___x_5197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5197_, 0, v_b_5194_);
                    return v___x_5197_;
                } else {
                    v_snd_5198_ = crate::leanh::lean_ctor_get(v_b_5194_, 1);
                    v_isSharedCheck_5216_ = (!crate::leanh::lean_is_exclusive(v_b_5194_)) as u8;
                    if v_isSharedCheck_5216_ == 0 {
                        v_unused_5217_ = crate::leanh::lean_ctor_get(v_b_5194_, 0);
                        crate::leanh::lean_dec(v_unused_5217_);
                        v___x_5200_ = v_b_5194_;
                        v_isShared_5201_ = v_isSharedCheck_5216_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5198_);
                        crate::leanh::lean_dec(v_b_5194_);
                        v___x_5200_ = crate::leanh::lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5216_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5202_ = crate::leanh::lean_box(0);
                v_a_5211_ = lean_array_uget_borrowed(v_as_5191_, v_i_5193_);
                if crate::leanh::lean_obj_tag(v_a_5211_) == 0 {
                    v_a_5204_ = v_snd_5198_;
                    state = 2;
                    continue;
                } else {
                    v_val_5212_ = crate::leanh::lean_ctor_get(v_a_5211_, 0);
                    v___x_5213_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5212_);
                    if v___x_5213_ == 0 {
                        v_a_5204_ = v_snd_5198_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5214_ = l_Lean_LocalDecl_fvarId(v_val_5212_);
                        v___x_5215_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5215_, 0, v___x_5214_);
                        crate::leanh::lean_ctor_set(v___x_5215_, 1, v_snd_5198_);
                        v_a_5204_ = v___x_5215_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5200_, 1, v_a_5204_);
                    crate::leanh::lean_ctor_set(v___x_5200_, 0, v___x_5202_);
                    v___x_5206_ = v___x_5200_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 1, v_a_5204_);
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
    mut v_as_5218_: *mut crate::leanh::LeanObject,
    mut v_sz_5219_: *mut crate::leanh::LeanObject,
    mut v_i_5220_: *mut crate::leanh::LeanObject,
    mut v_b_5221_: *mut crate::leanh::LeanObject,
    mut v___y_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5223_: usize = 0;
    let mut v_i_boxed_5224_: usize = 0;
    let mut v_res_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5223_ = crate::leanh::lean_unbox_usize(v_sz_5219_);
    crate::leanh::lean_dec(v_sz_5219_);
    v_i_boxed_5224_ = crate::leanh::lean_unbox_usize(v_i_5220_);
    crate::leanh::lean_dec(v_i_5220_);
    v_res_5225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_5218_, v_sz_boxed_5223_, v_i_boxed_5224_, v_b_5221_);
    crate::leanh::lean_dec_ref(v_as_5218_);
    return v_res_5225_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(
    mut v_as_5226_: *mut crate::leanh::LeanObject,
    mut v_sz_5227_: usize,
    mut v_i_5228_: usize,
    mut v_b_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5235_: u8 = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: usize = 0;
    let mut v___x_5247_: usize = 0;
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_unused_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = lean_usize_dec_lt(v_i_5228_, v_sz_5227_);
                if v___x_5235_ == 0 {
                    v___x_5236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5236_, 0, v_b_5229_);
                    return v___x_5236_;
                } else {
                    v_snd_5237_ = crate::leanh::lean_ctor_get(v_b_5229_, 1);
                    v_isSharedCheck_5255_ = (!crate::leanh::lean_is_exclusive(v_b_5229_)) as u8;
                    if v_isSharedCheck_5255_ == 0 {
                        v_unused_5256_ = crate::leanh::lean_ctor_get(v_b_5229_, 0);
                        crate::leanh::lean_dec(v_unused_5256_);
                        v___x_5239_ = v_b_5229_;
                        v_isShared_5240_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5237_);
                        crate::leanh::lean_dec(v_b_5229_);
                        v___x_5239_ = crate::leanh::lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5241_ = crate::leanh::lean_box(0);
                v_a_5250_ = lean_array_uget_borrowed(v_as_5226_, v_i_5228_);
                if crate::leanh::lean_obj_tag(v_a_5250_) == 0 {
                    v_a_5243_ = v_snd_5237_;
                    state = 2;
                    continue;
                } else {
                    v_val_5251_ = crate::leanh::lean_ctor_get(v_a_5250_, 0);
                    v___x_5252_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5251_);
                    if v___x_5252_ == 0 {
                        v_a_5243_ = v_snd_5237_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5253_ = l_Lean_LocalDecl_fvarId(v_val_5251_);
                        v___x_5254_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5254_, 0, v___x_5253_);
                        crate::leanh::lean_ctor_set(v___x_5254_, 1, v_snd_5237_);
                        v_a_5243_ = v___x_5254_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5239_, 1, v_a_5243_);
                    crate::leanh::lean_ctor_set(v___x_5239_, 0, v___x_5241_);
                    v___x_5245_ = v___x_5239_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5249_, 0, v___x_5241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5249_, 1, v_a_5243_);
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
    mut v_as_5257_: *mut crate::leanh::LeanObject,
    mut v_sz_5258_: *mut crate::leanh::LeanObject,
    mut v_i_5259_: *mut crate::leanh::LeanObject,
    mut v_b_5260_: *mut crate::leanh::LeanObject,
    mut v___y_5261_: *mut crate::leanh::LeanObject,
    mut v___y_5262_: *mut crate::leanh::LeanObject,
    mut v___y_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5266_: usize = 0;
    let mut v_i_boxed_5267_: usize = 0;
    let mut v_res_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5266_ = crate::leanh::lean_unbox_usize(v_sz_5258_);
    crate::leanh::lean_dec(v_sz_5258_);
    v_i_boxed_5267_ = crate::leanh::lean_unbox_usize(v_i_5259_);
    crate::leanh::lean_dec(v_i_5259_);
    v_res_5268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_5257_, v_sz_boxed_5266_, v_i_boxed_5267_, v_b_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
    crate::leanh::lean_dec(v___y_5264_);
    crate::leanh::lean_dec_ref(v___y_5263_);
    crate::leanh::lean_dec(v___y_5262_);
    crate::leanh::lean_dec_ref(v___y_5261_);
    crate::leanh::lean_dec_ref(v_as_5257_);
    return v_res_5268_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(
    mut v_init_5269_: *mut crate::leanh::LeanObject,
    mut v_n_5270_: *mut crate::leanh::LeanObject,
    mut v_b_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
    mut v___y_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5280_: usize = 0;
    let mut v___x_5281_: usize = 0;
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5286_: u8 = 0;
    let mut v_fst_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v_a_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v_vs_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5309_: usize = 0;
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v_fst_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_a_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5330_: u8 = 0;
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_5270_) == 0 {
                    v_cs_5277_ = crate::leanh::lean_ctor_get(v_n_5270_, 0);
                    v___x_5278_ = crate::leanh::lean_box(0);
                    v___x_5279_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5279_, 0, v___x_5278_);
                    crate::leanh::lean_ctor_set(v___x_5279_, 1, v_b_5271_);
                    v_sz_5280_ = lean_array_size(v_cs_5277_);
                    v___x_5281_ = 0usize;
                    v___x_5282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_5269_, v_cs_5277_, v_sz_5280_, v___x_5281_, v___x_5279_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
                    if crate::leanh::lean_obj_tag(v___x_5282_) == 0 {
                        v_a_5283_ = crate::leanh::lean_ctor_get(v___x_5282_, 0);
                        v_isSharedCheck_5297_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5282_)) as u8;
                        if v_isSharedCheck_5297_ == 0 {
                            v___x_5285_ = v___x_5282_;
                            v_isShared_5286_ = v_isSharedCheck_5297_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5283_);
                            crate::leanh::lean_dec(v___x_5282_);
                            v___x_5285_ = crate::leanh::lean_box(0);
                            v_isShared_5286_ = v_isSharedCheck_5297_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5298_ = crate::leanh::lean_ctor_get(v___x_5282_, 0);
                        v_isSharedCheck_5305_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5282_)) as u8;
                        if v_isSharedCheck_5305_ == 0 {
                            v___x_5300_ = v___x_5282_;
                            v_isShared_5301_ = v_isSharedCheck_5305_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5298_);
                            crate::leanh::lean_dec(v___x_5282_);
                            v___x_5300_ = crate::leanh::lean_box(0);
                            v_isShared_5301_ = v_isSharedCheck_5305_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5306_ = crate::leanh::lean_ctor_get(v_n_5270_, 0);
                    v___x_5307_ = crate::leanh::lean_box(0);
                    v___x_5308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5308_, 0, v___x_5307_);
                    crate::leanh::lean_ctor_set(v___x_5308_, 1, v_b_5271_);
                    v_sz_5309_ = lean_array_size(v_vs_5306_);
                    v___x_5310_ = 0usize;
                    v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_5306_, v_sz_5309_, v___x_5310_, v___x_5308_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
                    if crate::leanh::lean_obj_tag(v___x_5311_) == 0 {
                        v_a_5312_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5326_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5326_ == 0 {
                            v___x_5314_ = v___x_5311_;
                            v_isShared_5315_ = v_isSharedCheck_5326_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5312_);
                            crate::leanh::lean_dec(v___x_5311_);
                            v___x_5314_ = crate::leanh::lean_box(0);
                            v_isShared_5315_ = v_isSharedCheck_5326_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5327_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5334_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5334_ == 0 {
                            v___x_5329_ = v___x_5311_;
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5327_);
                            crate::leanh::lean_dec(v___x_5311_);
                            v___x_5329_ = crate::leanh::lean_box(0);
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5287_ = crate::leanh::lean_ctor_get(v_a_5283_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5287_) == 0 {
                    v_snd_5288_ = crate::leanh::lean_ctor_get(v_a_5283_, 1);
                    crate::leanh::lean_inc(v_snd_5288_);
                    crate::leanh::lean_dec(v_a_5283_);
                    v___x_5289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5289_, 0, v_snd_5288_);
                    if v_isShared_5286_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5285_, 0, v___x_5289_);
                        v___x_5291_ = v___x_5285_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
                        v___x_5291_ = v_reuseFailAlloc_5292_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5287_);
                    crate::leanh::lean_dec(v_a_5283_);
                    v_val_5293_ = crate::leanh::lean_ctor_get(v_fst_5287_, 0);
                    crate::leanh::lean_inc(v_val_5293_);
                    crate::leanh::lean_dec_ref_known(v_fst_5287_, 1);
                    if v_isShared_5286_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5285_, 0, v_val_5293_);
                        v___x_5295_ = v___x_5285_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5296_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_val_5293_);
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
                    v_reuseFailAlloc_5304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5303_;
            }
            6 => {
                v_fst_5316_ = crate::leanh::lean_ctor_get(v_a_5312_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5316_) == 0 {
                    v_snd_5317_ = crate::leanh::lean_ctor_get(v_a_5312_, 1);
                    crate::leanh::lean_inc(v_snd_5317_);
                    crate::leanh::lean_dec(v_a_5312_);
                    v___x_5318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5318_, 0, v_snd_5317_);
                    if v_isShared_5315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5314_, 0, v___x_5318_);
                        v___x_5320_ = v___x_5314_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5318_);
                        v___x_5320_ = v_reuseFailAlloc_5321_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5316_);
                    crate::leanh::lean_dec(v_a_5312_);
                    v_val_5322_ = crate::leanh::lean_ctor_get(v_fst_5316_, 0);
                    crate::leanh::lean_inc(v_val_5322_);
                    crate::leanh::lean_dec_ref_known(v_fst_5316_, 1);
                    if v_isShared_5315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5314_, 0, v_val_5322_);
                        v___x_5324_ = v___x_5314_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_val_5322_);
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
                    v_reuseFailAlloc_5333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
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
    mut v_init_5335_: *mut crate::leanh::LeanObject,
    mut v_as_5336_: *mut crate::leanh::LeanObject,
    mut v_sz_5337_: usize,
    mut v_i_5338_: usize,
    mut v_b_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5345_: u8 = 0;
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5350_: u8 = 0;
    let mut v_a_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5356_: u8 = 0;
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: usize = 0;
    let mut v___x_5369_: usize = 0;
    let mut v_reuseFailAlloc_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut v_a_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5376_: u8 = 0;
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5380_: u8 = 0;
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut v_unused_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5345_ = lean_usize_dec_lt(v_i_5338_, v_sz_5337_);
                if v___x_5345_ == 0 {
                    v___x_5346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5346_, 0, v_b_5339_);
                    return v___x_5346_;
                } else {
                    v_snd_5347_ = crate::leanh::lean_ctor_get(v_b_5339_, 1);
                    v_isSharedCheck_5381_ = (!crate::leanh::lean_is_exclusive(v_b_5339_)) as u8;
                    if v_isSharedCheck_5381_ == 0 {
                        v_unused_5382_ = crate::leanh::lean_ctor_get(v_b_5339_, 0);
                        crate::leanh::lean_dec(v_unused_5382_);
                        v___x_5349_ = v_b_5339_;
                        v_isShared_5350_ = v_isSharedCheck_5381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5347_);
                        crate::leanh::lean_dec(v_b_5339_);
                        v___x_5349_ = crate::leanh::lean_box(0);
                        v_isShared_5350_ = v_isSharedCheck_5381_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5351_ = lean_array_uget_borrowed(v_as_5336_, v_i_5338_);
                crate::leanh::lean_inc(v_snd_5347_);
                v___x_5352_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_5335_, v_a_5351_, v_snd_5347_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_);
                if crate::leanh::lean_obj_tag(v___x_5352_) == 0 {
                    v_a_5353_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
                    v_isSharedCheck_5372_ = (!crate::leanh::lean_is_exclusive(v___x_5352_)) as u8;
                    if v_isSharedCheck_5372_ == 0 {
                        v___x_5355_ = v___x_5352_;
                        v_isShared_5356_ = v_isSharedCheck_5372_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5353_);
                        crate::leanh::lean_dec(v___x_5352_);
                        v___x_5355_ = crate::leanh::lean_box(0);
                        v_isShared_5356_ = v_isSharedCheck_5372_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5349_);
                    crate::leanh::lean_dec(v_snd_5347_);
                    v_a_5373_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
                    v_isSharedCheck_5380_ = (!crate::leanh::lean_is_exclusive(v___x_5352_)) as u8;
                    if v_isSharedCheck_5380_ == 0 {
                        v___x_5375_ = v___x_5352_;
                        v_isShared_5376_ = v_isSharedCheck_5380_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5373_);
                        crate::leanh::lean_dec(v___x_5352_);
                        v___x_5375_ = crate::leanh::lean_box(0);
                        v_isShared_5376_ = v_isSharedCheck_5380_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5353_) == 0 {
                    v___x_5357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5357_, 0, v_a_5353_);
                    if v_isShared_5350_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5349_, 0, v___x_5357_);
                        v___x_5359_ = v___x_5349_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5363_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5357_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_snd_5347_);
                        v___x_5359_ = v_reuseFailAlloc_5363_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5355_);
                    crate::leanh::lean_dec(v_snd_5347_);
                    v_a_5364_ = crate::leanh::lean_ctor_get(v_a_5353_, 0);
                    crate::leanh::lean_inc(v_a_5364_);
                    crate::leanh::lean_dec_ref_known(v_a_5353_, 1);
                    v___x_5365_ = crate::leanh::lean_box(0);
                    if v_isShared_5350_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5349_, 1, v_a_5364_);
                        crate::leanh::lean_ctor_set(v___x_5349_, 0, v___x_5365_);
                        v___x_5367_ = v___x_5349_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5365_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 1, v_a_5364_);
                        v___x_5367_ = v_reuseFailAlloc_5371_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5355_, 0, v___x_5359_);
                    v___x_5361_ = v___x_5355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5362_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5359_);
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
                    v_reuseFailAlloc_5379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
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
    mut v_init_5383_: *mut crate::leanh::LeanObject,
    mut v_as_5384_: *mut crate::leanh::LeanObject,
    mut v_sz_5385_: *mut crate::leanh::LeanObject,
    mut v_i_5386_: *mut crate::leanh::LeanObject,
    mut v_b_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
    mut v___y_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5393_: usize = 0;
    let mut v_i_boxed_5394_: usize = 0;
    let mut v_res_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5393_ = crate::leanh::lean_unbox_usize(v_sz_5385_);
    crate::leanh::lean_dec(v_sz_5385_);
    v_i_boxed_5394_ = crate::leanh::lean_unbox_usize(v_i_5386_);
    crate::leanh::lean_dec(v_i_5386_);
    v_res_5395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_5383_, v_as_5384_, v_sz_boxed_5393_, v_i_boxed_5394_, v_b_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
    crate::leanh::lean_dec(v___y_5391_);
    crate::leanh::lean_dec_ref(v___y_5390_);
    crate::leanh::lean_dec(v___y_5389_);
    crate::leanh::lean_dec_ref(v___y_5388_);
    crate::leanh::lean_dec_ref(v_as_5384_);
    crate::leanh::lean_dec(v_init_5383_);
    return v_res_5395_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(
    mut v_init_5396_: *mut crate::leanh::LeanObject,
    mut v_n_5397_: *mut crate::leanh::LeanObject,
    mut v_b_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
    mut v___y_5400_: *mut crate::leanh::LeanObject,
    mut v___y_5401_: *mut crate::leanh::LeanObject,
    mut v___y_5402_: *mut crate::leanh::LeanObject,
    mut v___y_5403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5404_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_5396_, v_n_5397_, v_b_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_);
    crate::leanh::lean_dec(v___y_5402_);
    crate::leanh::lean_dec_ref(v___y_5401_);
    crate::leanh::lean_dec(v___y_5400_);
    crate::leanh::lean_dec_ref(v___y_5399_);
    crate::leanh::lean_dec_ref(v_n_5397_);
    crate::leanh::lean_dec(v_init_5396_);
    return v_res_5404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(
    mut v_as_5405_: *mut crate::leanh::LeanObject,
    mut v_sz_5406_: usize,
    mut v_i_5407_: usize,
    mut v_b_5408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5415_: u8 = 0;
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: usize = 0;
    let mut v___x_5422_: usize = 0;
    let mut v_reuseFailAlloc_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: u8 = 0;
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5430_: u8 = 0;
    let mut v_unused_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5410_ = lean_usize_dec_lt(v_i_5407_, v_sz_5406_);
                if v___x_5410_ == 0 {
                    v___x_5411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5411_, 0, v_b_5408_);
                    return v___x_5411_;
                } else {
                    v_snd_5412_ = crate::leanh::lean_ctor_get(v_b_5408_, 1);
                    v_isSharedCheck_5430_ = (!crate::leanh::lean_is_exclusive(v_b_5408_)) as u8;
                    if v_isSharedCheck_5430_ == 0 {
                        v_unused_5431_ = crate::leanh::lean_ctor_get(v_b_5408_, 0);
                        crate::leanh::lean_dec(v_unused_5431_);
                        v___x_5414_ = v_b_5408_;
                        v_isShared_5415_ = v_isSharedCheck_5430_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5412_);
                        crate::leanh::lean_dec(v_b_5408_);
                        v___x_5414_ = crate::leanh::lean_box(0);
                        v_isShared_5415_ = v_isSharedCheck_5430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5416_ = crate::leanh::lean_box(0);
                v_a_5425_ = lean_array_uget_borrowed(v_as_5405_, v_i_5407_);
                if crate::leanh::lean_obj_tag(v_a_5425_) == 0 {
                    v_a_5418_ = v_snd_5412_;
                    state = 2;
                    continue;
                } else {
                    v_val_5426_ = crate::leanh::lean_ctor_get(v_a_5425_, 0);
                    v___x_5427_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5426_);
                    if v___x_5427_ == 0 {
                        v_a_5418_ = v_snd_5412_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5428_ = l_Lean_LocalDecl_fvarId(v_val_5426_);
                        v___x_5429_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5429_, 0, v___x_5428_);
                        crate::leanh::lean_ctor_set(v___x_5429_, 1, v_snd_5412_);
                        v_a_5418_ = v___x_5429_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5414_, 1, v_a_5418_);
                    crate::leanh::lean_ctor_set(v___x_5414_, 0, v___x_5416_);
                    v___x_5420_ = v___x_5414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 0, v___x_5416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_a_5418_);
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
    mut v_as_5432_: *mut crate::leanh::LeanObject,
    mut v_sz_5433_: *mut crate::leanh::LeanObject,
    mut v_i_5434_: *mut crate::leanh::LeanObject,
    mut v_b_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5437_: usize = 0;
    let mut v_i_boxed_5438_: usize = 0;
    let mut v_res_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5437_ = crate::leanh::lean_unbox_usize(v_sz_5433_);
    crate::leanh::lean_dec(v_sz_5433_);
    v_i_boxed_5438_ = crate::leanh::lean_unbox_usize(v_i_5434_);
    crate::leanh::lean_dec(v_i_5434_);
    v_res_5439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_5432_, v_sz_boxed_5437_, v_i_boxed_5438_, v_b_5435_);
    crate::leanh::lean_dec_ref(v_as_5432_);
    return v_res_5439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(
    mut v_as_5440_: *mut crate::leanh::LeanObject,
    mut v_sz_5441_: usize,
    mut v_i_5442_: usize,
    mut v_b_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
    mut v___y_5447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: usize = 0;
    let mut v___x_5461_: usize = 0;
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v_unused_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5449_ = lean_usize_dec_lt(v_i_5442_, v_sz_5441_);
                if v___x_5449_ == 0 {
                    v___x_5450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5450_, 0, v_b_5443_);
                    return v___x_5450_;
                } else {
                    v_snd_5451_ = crate::leanh::lean_ctor_get(v_b_5443_, 1);
                    v_isSharedCheck_5469_ = (!crate::leanh::lean_is_exclusive(v_b_5443_)) as u8;
                    if v_isSharedCheck_5469_ == 0 {
                        v_unused_5470_ = crate::leanh::lean_ctor_get(v_b_5443_, 0);
                        crate::leanh::lean_dec(v_unused_5470_);
                        v___x_5453_ = v_b_5443_;
                        v_isShared_5454_ = v_isSharedCheck_5469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5451_);
                        crate::leanh::lean_dec(v_b_5443_);
                        v___x_5453_ = crate::leanh::lean_box(0);
                        v_isShared_5454_ = v_isSharedCheck_5469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5455_ = crate::leanh::lean_box(0);
                v_a_5464_ = lean_array_uget_borrowed(v_as_5440_, v_i_5442_);
                if crate::leanh::lean_obj_tag(v_a_5464_) == 0 {
                    v_a_5457_ = v_snd_5451_;
                    state = 2;
                    continue;
                } else {
                    v_val_5465_ = crate::leanh::lean_ctor_get(v_a_5464_, 0);
                    v___x_5466_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5465_);
                    if v___x_5466_ == 0 {
                        v_a_5457_ = v_snd_5451_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5467_ = l_Lean_LocalDecl_fvarId(v_val_5465_);
                        v___x_5468_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5468_, 0, v___x_5467_);
                        crate::leanh::lean_ctor_set(v___x_5468_, 1, v_snd_5451_);
                        v_a_5457_ = v___x_5468_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5454_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5453_, 1, v_a_5457_);
                    crate::leanh::lean_ctor_set(v___x_5453_, 0, v___x_5455_);
                    v___x_5459_ = v___x_5453_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 1, v_a_5457_);
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
    mut v_as_5471_: *mut crate::leanh::LeanObject,
    mut v_sz_5472_: *mut crate::leanh::LeanObject,
    mut v_i_5473_: *mut crate::leanh::LeanObject,
    mut v_b_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5480_: usize = 0;
    let mut v_i_boxed_5481_: usize = 0;
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5480_ = crate::leanh::lean_unbox_usize(v_sz_5472_);
    crate::leanh::lean_dec(v_sz_5472_);
    v_i_boxed_5481_ = crate::leanh::lean_unbox_usize(v_i_5473_);
    crate::leanh::lean_dec(v_i_5473_);
    v_res_5482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_5471_, v_sz_boxed_5480_, v_i_boxed_5481_, v_b_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_);
    crate::leanh::lean_dec(v___y_5478_);
    crate::leanh::lean_dec_ref(v___y_5477_);
    crate::leanh::lean_dec(v___y_5476_);
    crate::leanh::lean_dec_ref(v___y_5475_);
    crate::leanh::lean_dec_ref(v_as_5471_);
    return v_res_5482_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(
    mut v_t_5483_: *mut crate::leanh::LeanObject,
    mut v_init_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v_a_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5504_: usize = 0;
    let mut v___x_5505_: usize = 0;
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v_fst_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_a_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_isSharedCheck_5529_: u8 = 0;
    let mut v_a_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5533_: u8 = 0;
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5490_ = crate::leanh::lean_ctor_get(v_t_5483_, 0);
                v_tail_5491_ = crate::leanh::lean_ctor_get(v_t_5483_, 1);
                crate::leanh::lean_inc(v_init_5484_);
                v___x_5492_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_5484_, v_root_5490_, v_init_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
                crate::leanh::lean_dec(v_init_5484_);
                if crate::leanh::lean_obj_tag(v___x_5492_) == 0 {
                    v_a_5493_ = crate::leanh::lean_ctor_get(v___x_5492_, 0);
                    v_isSharedCheck_5529_ = (!crate::leanh::lean_is_exclusive(v___x_5492_)) as u8;
                    if v_isSharedCheck_5529_ == 0 {
                        v___x_5495_ = v___x_5492_;
                        v_isShared_5496_ = v_isSharedCheck_5529_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5493_);
                        crate::leanh::lean_dec(v___x_5492_);
                        v___x_5495_ = crate::leanh::lean_box(0);
                        v_isShared_5496_ = v_isSharedCheck_5529_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5530_ = crate::leanh::lean_ctor_get(v___x_5492_, 0);
                    v_isSharedCheck_5537_ = (!crate::leanh::lean_is_exclusive(v___x_5492_)) as u8;
                    if v_isSharedCheck_5537_ == 0 {
                        v___x_5532_ = v___x_5492_;
                        v_isShared_5533_ = v_isSharedCheck_5537_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5530_);
                        crate::leanh::lean_dec(v___x_5492_);
                        v___x_5532_ = crate::leanh::lean_box(0);
                        v_isShared_5533_ = v_isSharedCheck_5537_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5493_) == 0 {
                    v_a_5497_ = crate::leanh::lean_ctor_get(v_a_5493_, 0);
                    crate::leanh::lean_inc(v_a_5497_);
                    crate::leanh::lean_dec_ref_known(v_a_5493_, 1);
                    if v_isShared_5496_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5495_, 0, v_a_5497_);
                        v___x_5499_ = v___x_5495_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5500_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5497_);
                        v___x_5499_ = v_reuseFailAlloc_5500_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5495_);
                    v_a_5501_ = crate::leanh::lean_ctor_get(v_a_5493_, 0);
                    crate::leanh::lean_inc(v_a_5501_);
                    crate::leanh::lean_dec_ref_known(v_a_5493_, 1);
                    v___x_5502_ = crate::leanh::lean_box(0);
                    v___x_5503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5503_, 0, v___x_5502_);
                    crate::leanh::lean_ctor_set(v___x_5503_, 1, v_a_5501_);
                    v_sz_5504_ = lean_array_size(v_tail_5491_);
                    v___x_5505_ = 0usize;
                    v___x_5506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_5491_, v_sz_5504_, v___x_5505_, v___x_5503_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
                    if crate::leanh::lean_obj_tag(v___x_5506_) == 0 {
                        v_a_5507_ = crate::leanh::lean_ctor_get(v___x_5506_, 0);
                        v_isSharedCheck_5520_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5506_)) as u8;
                        if v_isSharedCheck_5520_ == 0 {
                            v___x_5509_ = v___x_5506_;
                            v_isShared_5510_ = v_isSharedCheck_5520_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5507_);
                            crate::leanh::lean_dec(v___x_5506_);
                            v___x_5509_ = crate::leanh::lean_box(0);
                            v_isShared_5510_ = v_isSharedCheck_5520_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5521_ = crate::leanh::lean_ctor_get(v___x_5506_, 0);
                        v_isSharedCheck_5528_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5506_)) as u8;
                        if v_isSharedCheck_5528_ == 0 {
                            v___x_5523_ = v___x_5506_;
                            v_isShared_5524_ = v_isSharedCheck_5528_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5521_);
                            crate::leanh::lean_dec(v___x_5506_);
                            v___x_5523_ = crate::leanh::lean_box(0);
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
                v_fst_5511_ = crate::leanh::lean_ctor_get(v_a_5507_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5511_) == 0 {
                    v_snd_5512_ = crate::leanh::lean_ctor_get(v_a_5507_, 1);
                    crate::leanh::lean_inc(v_snd_5512_);
                    crate::leanh::lean_dec(v_a_5507_);
                    if v_isShared_5510_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5509_, 0, v_snd_5512_);
                        v___x_5514_ = v___x_5509_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_snd_5512_);
                        v___x_5514_ = v_reuseFailAlloc_5515_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5511_);
                    crate::leanh::lean_dec(v_a_5507_);
                    v_val_5516_ = crate::leanh::lean_ctor_get(v_fst_5511_, 0);
                    crate::leanh::lean_inc(v_val_5516_);
                    crate::leanh::lean_dec_ref_known(v_fst_5511_, 1);
                    if v_isShared_5510_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5509_, 0, v_val_5516_);
                        v___x_5518_ = v___x_5509_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5519_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_val_5516_);
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
                    v_reuseFailAlloc_5527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
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
                    v_reuseFailAlloc_5536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
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
    mut v_t_5538_: *mut crate::leanh::LeanObject,
    mut v_init_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5545_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(
        v_t_5538_,
        v_init_5539_,
        v___y_5540_,
        v___y_5541_,
        v___y_5542_,
        v___y_5543_,
    );
    crate::leanh::lean_dec(v___y_5543_);
    crate::leanh::lean_dec_ref(v___y_5542_);
    crate::leanh::lean_dec(v___y_5541_);
    crate::leanh::lean_dec_ref(v___y_5540_);
    crate::leanh::lean_dec_ref(v_t_5538_);
    return v_res_5545_;
}
pub unsafe fn l_Lean_MVarId_clearImplDetails___lam__0(
    mut v_mvarId_5546_: *mut crate::leanh::LeanObject,
    mut v___x_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5562_: u8 = 0;
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut v_a_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v_a_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5579_: u8 = 0;
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_5546_);
                v___x_5553_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5546_,
                    v___x_5547_,
                    v___y_5548_,
                    v___y_5549_,
                    v___y_5550_,
                    v___y_5551_,
                );
                if crate::leanh::lean_obj_tag(v___x_5553_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5553_, 1);
                    v_lctx_5554_ = crate::leanh::lean_ctor_get(v___y_5548_, 2);
                    v_decls_5555_ = crate::leanh::lean_ctor_get(v_lctx_5554_, 1);
                    v___x_5556_ = crate::leanh::lean_box(0);
                    v___x_5557_ =
                        l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(
                            v_decls_5555_,
                            v___x_5556_,
                            v___y_5548_,
                            v___y_5549_,
                            v___y_5550_,
                            v___y_5551_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5557_) == 0 {
                        v_a_5558_ = crate::leanh::lean_ctor_get(v___x_5557_, 0);
                        v_isSharedCheck_5567_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5557_)) as u8;
                        if v_isSharedCheck_5567_ == 0 {
                            v___x_5560_ = v___x_5557_;
                            v_isShared_5561_ = v_isSharedCheck_5567_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5558_);
                            crate::leanh::lean_dec(v___x_5557_);
                            v___x_5560_ = crate::leanh::lean_box(0);
                            v_isShared_5561_ = v_isSharedCheck_5567_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_5546_);
                        v_a_5568_ = crate::leanh::lean_ctor_get(v___x_5557_, 0);
                        v_isSharedCheck_5575_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5557_)) as u8;
                        if v_isSharedCheck_5575_ == 0 {
                            v___x_5570_ = v___x_5557_;
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5568_);
                            crate::leanh::lean_dec(v___x_5557_);
                            v___x_5570_ = crate::leanh::lean_box(0);
                            v_isShared_5571_ = v_isSharedCheck_5575_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_5546_);
                    v_a_5576_ = crate::leanh::lean_ctor_get(v___x_5553_, 0);
                    v_isSharedCheck_5583_ = (!crate::leanh::lean_is_exclusive(v___x_5553_)) as u8;
                    if v_isSharedCheck_5583_ == 0 {
                        v___x_5578_ = v___x_5553_;
                        v_isShared_5579_ = v_isSharedCheck_5583_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5576_);
                        crate::leanh::lean_dec(v___x_5553_);
                        v___x_5578_ = crate::leanh::lean_box(0);
                        v_isShared_5579_ = v_isSharedCheck_5583_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5562_ = l_List_isEmpty___redArg(v_a_5558_);
                if v___x_5562_ == 0 {
                    crate::leanh::lean_del_object(v___x_5560_);
                    v___x_5563_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_5558_, v_mvarId_5546_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
                    crate::leanh::lean_dec(v_a_5558_);
                    return v___x_5563_;
                } else {
                    crate::leanh::lean_dec(v_a_5558_);
                    if v_isShared_5561_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5560_, 0, v_mvarId_5546_);
                        v___x_5565_ = v___x_5560_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_mvarId_5546_);
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
                    v_reuseFailAlloc_5574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
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
                    v_reuseFailAlloc_5582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
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
    mut v_mvarId_5584_: *mut crate::leanh::LeanObject,
    mut v___x_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5591_ = l_Lean_MVarId_clearImplDetails___lam__0(
        v_mvarId_5584_,
        v___x_5585_,
        v___y_5586_,
        v___y_5587_,
        v___y_5588_,
        v___y_5589_,
    );
    crate::leanh::lean_dec(v___y_5589_);
    crate::leanh::lean_dec_ref(v___y_5588_);
    crate::leanh::lean_dec(v___y_5587_);
    crate::leanh::lean_dec_ref(v___y_5586_);
    return v_res_5591_;
}
pub unsafe fn l_Lean_MVarId_clearImplDetails(
    mut v_mvarId_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
    mut v_a_5598_: *mut crate::leanh::LeanObject,
    mut v_a_5599_: *mut crate::leanh::LeanObject,
    mut v_a_5600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5602_ = l_Lean_MVarId_clearImplDetails___closed__1;
    crate::leanh::lean_inc(v_mvarId_5596_);
    v___f_5603_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_clearImplDetails___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5603_, 0, v_mvarId_5596_);
    crate::leanh::lean_closure_set(v___f_5603_, 1, v___x_5602_);
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
    mut v_mvarId_5605_: *mut crate::leanh::LeanObject,
    mut v_a_5606_: *mut crate::leanh::LeanObject,
    mut v_a_5607_: *mut crate::leanh::LeanObject,
    mut v_a_5608_: *mut crate::leanh::LeanObject,
    mut v_a_5609_: *mut crate::leanh::LeanObject,
    mut v_a_5610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5611_ =
        l_Lean_MVarId_clearImplDetails(v_mvarId_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
    crate::leanh::lean_dec(v_a_5609_);
    crate::leanh::lean_dec_ref(v_a_5608_);
    crate::leanh::lean_dec(v_a_5607_);
    crate::leanh::lean_dec_ref(v_a_5606_);
    return v_res_5611_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(
    mut v_as_5612_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5613_: *mut crate::leanh::LeanObject,
    mut v_b_5614_: *mut crate::leanh::LeanObject,
    mut v_a_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_5622_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5623_: *mut crate::leanh::LeanObject,
    mut v_b_5624_: *mut crate::leanh::LeanObject,
    mut v_a_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_5629_);
    crate::leanh::lean_dec_ref(v___y_5628_);
    crate::leanh::lean_dec(v___y_5627_);
    crate::leanh::lean_dec_ref(v___y_5626_);
    crate::leanh::lean_dec(v_as_x27_5623_);
    crate::leanh::lean_dec(v_as_5622_);
    return v_res_5631_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(
    mut v_as_5632_: *mut crate::leanh::LeanObject,
    mut v_sz_5633_: usize,
    mut v_i_5634_: usize,
    mut v_b_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_5632_, v_sz_5633_, v_i_5634_, v_b_5635_);
    return v___x_5641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(
    mut v_as_5642_: *mut crate::leanh::LeanObject,
    mut v_sz_5643_: *mut crate::leanh::LeanObject,
    mut v_i_5644_: *mut crate::leanh::LeanObject,
    mut v_b_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5651_: usize = 0;
    let mut v_i_boxed_5652_: usize = 0;
    let mut v_res_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5651_ = crate::leanh::lean_unbox_usize(v_sz_5643_);
    crate::leanh::lean_dec(v_sz_5643_);
    v_i_boxed_5652_ = crate::leanh::lean_unbox_usize(v_i_5644_);
    crate::leanh::lean_dec(v_i_5644_);
    v_res_5653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_5642_, v_sz_boxed_5651_, v_i_boxed_5652_, v_b_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
    crate::leanh::lean_dec(v___y_5649_);
    crate::leanh::lean_dec_ref(v___y_5648_);
    crate::leanh::lean_dec(v___y_5647_);
    crate::leanh::lean_dec_ref(v___y_5646_);
    crate::leanh::lean_dec_ref(v_as_5642_);
    return v_res_5653_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(
    mut v_as_5654_: *mut crate::leanh::LeanObject,
    mut v_sz_5655_: usize,
    mut v_i_5656_: usize,
    mut v_b_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
    mut v___y_5660_: *mut crate::leanh::LeanObject,
    mut v___y_5661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_5654_, v_sz_5655_, v_i_5656_, v_b_5657_);
    return v___x_5663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_as_5664_: *mut crate::leanh::LeanObject,
    mut v_sz_5665_: *mut crate::leanh::LeanObject,
    mut v_i_5666_: *mut crate::leanh::LeanObject,
    mut v_b_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5673_: usize = 0;
    let mut v_i_boxed_5674_: usize = 0;
    let mut v_res_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5673_ = crate::leanh::lean_unbox_usize(v_sz_5665_);
    crate::leanh::lean_dec(v_sz_5665_);
    v_i_boxed_5674_ = crate::leanh::lean_unbox_usize(v_i_5666_);
    crate::leanh::lean_dec(v_i_5666_);
    v_res_5675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_5664_, v_sz_boxed_5673_, v_i_boxed_5674_, v_b_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
    crate::leanh::lean_dec(v___y_5671_);
    crate::leanh::lean_dec_ref(v___y_5670_);
    crate::leanh::lean_dec(v___y_5669_);
    crate::leanh::lean_dec_ref(v___y_5668_);
    crate::leanh::lean_dec_ref(v_as_5664_);
    return v_res_5675_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(
    mut v_e_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_5676_) {
        8 => {
            let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5680_, 0, v_e_5676_);
            v___x_5681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5681_, 0, v___x_5680_);
            return v___x_5681_;
        }
        6 => {
            let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5682_, 0, v_e_5676_);
            v___x_5683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5683_, 0, v___x_5682_);
            return v___x_5683_;
        }
        10 => {
            let mut v_expr_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_expr_5684_ = crate::leanh::lean_ctor_get(v_e_5676_, 1);
            crate::leanh::lean_inc_ref(v_expr_5684_);
            crate::leanh::lean_dec_ref_known(v_e_5676_, 2);
            v___x_5685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5685_, 0, v_expr_5684_);
            v___x_5686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5686_, 0, v___x_5685_);
            return v___x_5686_;
        }
        _ => {
            let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5687_, 0, v_e_5676_);
            v___x_5688_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5688_, 0, v___x_5687_);
            v___x_5689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5689_, 0, v___x_5688_);
            return v___x_5689_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(
    mut v_e_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5694_ =
        l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_5690_, v___y_5691_, v___y_5692_);
    crate::leanh::lean_dec(v___y_5692_);
    crate::leanh::lean_dec_ref(v___y_5691_);
    return v_res_5694_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(
    mut v_e_5695_: *mut crate::leanh::LeanObject,
    mut v___y_5696_: *mut crate::leanh::LeanObject,
    mut v___y_5697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5699_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5699_, 0, v_e_5695_);
    v___x_5700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5700_, 0, v___x_5699_);
    return v___x_5700_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(
    mut v_e_5701_: *mut crate::leanh::LeanObject,
    mut v___y_5702_: *mut crate::leanh::LeanObject,
    mut v___y_5703_: *mut crate::leanh::LeanObject,
    mut v___y_5704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5705_ =
        l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_5701_, v___y_5702_, v___y_5703_);
    crate::leanh::lean_dec(v___y_5703_);
    crate::leanh::lean_dec_ref(v___y_5702_);
    return v_res_5705_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(
    mut v_00_u03b1_5706_: *mut crate::leanh::LeanObject,
    mut v_x_5707_: *mut crate::leanh::LeanObject,
    mut v___y_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5711_ = crate::leanh::lean_apply_1(v_x_5707_, crate::leanh::lean_box(0));
    v___x_5712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5712_, 0, v___x_5711_);
    return v___x_5712_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(
    mut v_00_u03b1_5713_: *mut crate::leanh::LeanObject,
    mut v_x_5714_: *mut crate::leanh::LeanObject,
    mut v___y_5715_: *mut crate::leanh::LeanObject,
    mut v___y_5716_: *mut crate::leanh::LeanObject,
    mut v___y_5717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5718_ =
        l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(
            v_00_u03b1_5713_,
            v_x_5714_,
            v___y_5715_,
            v___y_5716_,
        );
    crate::leanh::lean_dec(v___y_5716_);
    crate::leanh::lean_dec_ref(v___y_5715_);
    return v_res_5718_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(
    mut v_a_5719_: *mut crate::leanh::LeanObject,
    mut v_x_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: u8 = 0;
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5720_) == 0 {
                    v___x_5721_ = crate::leanh::lean_box(0);
                    return v___x_5721_;
                } else {
                    v_key_5722_ = crate::leanh::lean_ctor_get(v_x_5720_, 0);
                    v_value_5723_ = crate::leanh::lean_ctor_get(v_x_5720_, 1);
                    v_tail_5724_ = crate::leanh::lean_ctor_get(v_x_5720_, 2);
                    v___x_5725_ = l_Lean_ExprStructEq_beq(v_key_5722_, v_a_5719_);
                    if v___x_5725_ == 0 {
                        v_x_5720_ = v_tail_5724_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5723_);
                        v___x_5727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5727_, 0, v_value_5723_);
                        return v___x_5727_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(
    mut v_a_5728_: *mut crate::leanh::LeanObject,
    mut v_x_5729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5730_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_5728_, v_x_5729_);
    crate::leanh::lean_dec(v_x_5729_);
    crate::leanh::lean_dec_ref(v_a_5728_);
    return v_res_5730_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(
    mut v_m_5731_: *mut crate::leanh::LeanObject,
    mut v_a_5732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5733_ = crate::leanh::lean_ctor_get(v_m_5731_, 1);
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
    mut v_m_5749_: *mut crate::leanh::LeanObject,
    mut v_a_5750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_5749_, v_a_5750_);
    crate::leanh::lean_dec_ref(v_a_5750_);
    crate::leanh::lean_dec_ref(v_m_5749_);
    return v_res_5751_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(
    mut v_00_u03b1_5752_: *mut crate::leanh::LeanObject,
    mut v_x_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5757_ = crate::leanh::lean_apply_1(v_x_5753_, crate::leanh::lean_box(0));
    v___x_5758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_5759_: *mut crate::leanh::LeanObject,
    mut v_x_5760_: *mut crate::leanh::LeanObject,
    mut v___y_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5764_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_5759_, v_x_5760_, v___y_5761_, v___y_5762_);
    crate::leanh::lean_dec(v___y_5762_);
    crate::leanh::lean_dec_ref(v___y_5761_);
    return v_res_5764_;
}
pub unsafe fn _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = crate::leanh::lean_box(0);
    v___x_5766_ = l_Lean_interruptExceptionId;
    v___x_5767_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5767_, 0, v___x_5766_);
    crate::leanh::lean_ctor_set(v___x_5767_, 1, v___x_5765_);
    return v___x_5767_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___closed__0);
    v___x_5770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5770_, 0, v___x_5769_);
    return v___x_5770_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg___boxed(
    mut v___y_5771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5772_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
    return v_res_5772_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5778_ = l_Lean_maxRecDepthErrorMessage;
    v___x_5779_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
    return v___x_5779_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5780_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
    v___x_5781_ = l_Lean_MessageData_ofFormat(v___x_5780_);
    return v___x_5781_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
    v___x_5783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2;
    v___x_5784_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5784_, 0, v___x_5783_);
    crate::leanh::lean_ctor_set(v___x_5784_, 1, v___x_5782_);
    return v___x_5784_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(
    mut v_ref_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5787_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
    v___x_5788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5788_, 0, v_ref_5785_);
    crate::leanh::lean_ctor_set(v___x_5788_, 1, v___x_5787_);
    v___x_5789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5789_, 0, v___x_5788_);
    return v___x_5789_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(
    mut v_ref_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5792_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_5790_);
    return v_res_5792_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(
    mut v_x_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v___y_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: u8 = 0;
    let mut v___y_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5812_: u8 = 0;
    let mut v___y_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5841_: u8 = 0;
    let mut v_cancelTk_x3f_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5843_: u8 = 0;
    let mut v_inheritedTraceOptions_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: u8 = 0;
    let mut v___x_5848_: u8 = 0;
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: u8 = 0;
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5829_ = crate::leanh::lean_ctor_get(v___y_5795_, 0);
                v_fileMap_5830_ = crate::leanh::lean_ctor_get(v___y_5795_, 1);
                v_options_5831_ = crate::leanh::lean_ctor_get(v___y_5795_, 2);
                v_currRecDepth_5832_ = crate::leanh::lean_ctor_get(v___y_5795_, 3);
                v_maxRecDepth_5833_ = crate::leanh::lean_ctor_get(v___y_5795_, 4);
                v_ref_5834_ = crate::leanh::lean_ctor_get(v___y_5795_, 5);
                v_currNamespace_5835_ = crate::leanh::lean_ctor_get(v___y_5795_, 6);
                v_openDecls_5836_ = crate::leanh::lean_ctor_get(v___y_5795_, 7);
                v_initHeartbeats_5837_ = crate::leanh::lean_ctor_get(v___y_5795_, 8);
                v_maxHeartbeats_5838_ = crate::leanh::lean_ctor_get(v___y_5795_, 9);
                v_quotContext_5839_ = crate::leanh::lean_ctor_get(v___y_5795_, 10);
                v_currMacroScope_5840_ = crate::leanh::lean_ctor_get(v___y_5795_, 11);
                v_diag_5841_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5795_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5842_ = crate::leanh::lean_ctor_get(v___y_5795_, 12);
                v_suppressElabErrors_5843_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5795_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5844_ = crate::leanh::lean_ctor_get(v___y_5795_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_5842_) == 1 {
                    v_val_5850_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_5842_, 0);
                    v___x_5851_ = l_IO_CancelToken_isSet(v_val_5850_);
                    if v___x_5851_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_5793_);
                        v___x_5852_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_5853_ = crate::leanh::lean_ctor_get(v___x_5852_, 0);
                        v_isSharedCheck_5860_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5852_)) as u8;
                        if v_isSharedCheck_5860_ == 0 {
                            v___x_5855_ = v___x_5852_;
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5853_);
                            crate::leanh::lean_dec(v___x_5852_);
                            v___x_5855_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___y_5799_) == 0 {
                    return v___y_5799_;
                } else {
                    v_a_5800_ = crate::leanh::lean_ctor_get(v___y_5799_, 0);
                    v_isSharedCheck_5807_ = (!crate::leanh::lean_is_exclusive(v___y_5799_)) as u8;
                    if v_isSharedCheck_5807_ == 0 {
                        v___x_5802_ = v___y_5799_;
                        v_isShared_5803_ = v_isSharedCheck_5807_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5800_);
                        crate::leanh::lean_dec(v___y_5799_);
                        v___x_5802_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
                    v___x_5805_ = v_reuseFailAlloc_5806_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5805_;
            }
            4 => {
                v___x_5825_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5826_ = lean_nat_add(v___y_5814_, v___x_5825_);
                crate::leanh::lean_inc_ref(v___y_5821_);
                crate::leanh::lean_inc(v___y_5813_);
                crate::leanh::lean_inc(v___y_5817_);
                crate::leanh::lean_inc(v___y_5824_);
                crate::leanh::lean_inc(v___y_5823_);
                crate::leanh::lean_inc(v___y_5815_);
                crate::leanh::lean_inc(v___y_5820_);
                crate::leanh::lean_inc(v___y_5816_);
                crate::leanh::lean_inc(v___y_5811_);
                crate::leanh::lean_inc_ref(v___y_5809_);
                crate::leanh::lean_inc_ref(v___y_5818_);
                crate::leanh::lean_inc_ref(v___y_5819_);
                v___x_5827_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_5827_, 0, v___y_5819_);
                crate::leanh::lean_ctor_set(v___x_5827_, 1, v___y_5818_);
                crate::leanh::lean_ctor_set(v___x_5827_, 2, v___y_5809_);
                crate::leanh::lean_ctor_set(v___x_5827_, 3, v___x_5826_);
                crate::leanh::lean_ctor_set(v___x_5827_, 4, v___y_5811_);
                crate::leanh::lean_ctor_set(v___x_5827_, 5, v___y_5822_);
                crate::leanh::lean_ctor_set(v___x_5827_, 6, v___y_5816_);
                crate::leanh::lean_ctor_set(v___x_5827_, 7, v___y_5820_);
                crate::leanh::lean_ctor_set(v___x_5827_, 8, v___y_5815_);
                crate::leanh::lean_ctor_set(v___x_5827_, 9, v___y_5823_);
                crate::leanh::lean_ctor_set(v___x_5827_, 10, v___y_5824_);
                crate::leanh::lean_ctor_set(v___x_5827_, 11, v___y_5817_);
                crate::leanh::lean_ctor_set(v___x_5827_, 12, v___y_5813_);
                crate::leanh::lean_ctor_set(v___x_5827_, 13, v___y_5821_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5827_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_5812_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5827_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_5810_,
                );
                crate::leanh::lean_inc(v___y_5796_);
                crate::leanh::lean_inc(v___y_5794_);
                v___x_5828_ = crate::leanh::lean_apply_4(
                    v_x_5793_,
                    v___y_5794_,
                    v___x_5827_,
                    v___y_5796_,
                    crate::leanh::lean_box(0),
                );
                v___y_5799_ = v___x_5828_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5846_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5847_ = lean_nat_dec_eq(v_maxRecDepth_5833_, v___x_5846_);
                if v___x_5847_ == 0 {
                    v___x_5848_ = lean_nat_dec_eq(v_currRecDepth_5832_, v_maxRecDepth_5833_);
                    if v___x_5848_ == 0 {
                        crate::leanh::lean_inc(v_ref_5834_);
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
                        crate::leanh::lean_dec_ref(v_x_5793_);
                        crate::leanh::lean_inc(v_ref_5834_);
                        v___x_5849_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_5834_);
                        v___y_5799_ = v___x_5849_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_5834_);
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
                    v_reuseFailAlloc_5859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
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
    mut v_x_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_5861_, v___y_5862_, v___y_5863_, v___y_5864_);
    crate::leanh::lean_dec(v___y_5864_);
    crate::leanh::lean_dec_ref(v___y_5863_);
    crate::leanh::lean_dec(v___y_5862_);
    return v_res_5866_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(
    mut v_x_5867_: *mut crate::leanh::LeanObject,
    mut v_x_5868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5868_) == 0 {
                    return v_x_5867_;
                } else {
                    v_key_5869_ = crate::leanh::lean_ctor_get(v_x_5868_, 0);
                    v_value_5870_ = crate::leanh::lean_ctor_get(v_x_5868_, 1);
                    v_tail_5871_ = crate::leanh::lean_ctor_get(v_x_5868_, 2);
                    v_isSharedCheck_5894_ = (!crate::leanh::lean_is_exclusive(v_x_5868_)) as u8;
                    if v_isSharedCheck_5894_ == 0 {
                        v___x_5873_ = v_x_5868_;
                        v_isShared_5874_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5871_);
                        crate::leanh::lean_inc(v_value_5870_);
                        crate::leanh::lean_inc(v_key_5869_);
                        crate::leanh::lean_dec(v_x_5868_);
                        v___x_5873_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_inc(v___x_5888_);
                if v_isShared_5874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5873_, 2, v___x_5888_);
                    v___x_5890_ = v___x_5873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_key_5869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 1, v_value_5870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 2, v___x_5888_);
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
    mut v_i_5895_: *mut crate::leanh::LeanObject,
    mut v_source_5896_: *mut crate::leanh::LeanObject,
    mut v_target_5897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    let mut v_es_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5898_ = lean_array_get_size(v_source_5896_);
                v___x_5899_ = lean_nat_dec_lt(v_i_5895_, v___x_5898_);
                if v___x_5899_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5896_);
                    crate::leanh::lean_dec(v_i_5895_);
                    return v_target_5897_;
                } else {
                    v_es_5900_ = lean_array_fget(v_source_5896_, v_i_5895_);
                    v___x_5901_ = crate::leanh::lean_box(0);
                    v_source_5902_ = lean_array_fset(v_source_5896_, v_i_5895_, v___x_5901_);
                    v_target_5903_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_target_5897_, v_es_5900_);
                    v___x_5904_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5905_ = lean_nat_add(v_i_5895_, v___x_5904_);
                    crate::leanh::lean_dec(v_i_5895_);
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
    mut v_data_5907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5908_ = lean_array_get_size(v_data_5907_);
    v___x_5909_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5910_ = lean_nat_mul(v___x_5908_, v___x_5909_);
    v___x_5911_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5912_ = crate::leanh::lean_box(0);
    v___x_5913_ = lean_mk_array(v_nbuckets_5910_, v___x_5912_);
    v___x_5914_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v___x_5911_, v_data_5907_, v___x_5913_);
    return v___x_5914_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(
    mut v_a_5915_: *mut crate::leanh::LeanObject,
    mut v_b_5916_: *mut crate::leanh::LeanObject,
    mut v_x_5917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5923_: u8 = 0;
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5917_) == 0 {
                    crate::leanh::lean_dec(v_b_5916_);
                    crate::leanh::lean_dec_ref(v_a_5915_);
                    return v_x_5917_;
                } else {
                    v_key_5918_ = crate::leanh::lean_ctor_get(v_x_5917_, 0);
                    v_value_5919_ = crate::leanh::lean_ctor_get(v_x_5917_, 1);
                    v_tail_5920_ = crate::leanh::lean_ctor_get(v_x_5917_, 2);
                    v_isSharedCheck_5932_ = (!crate::leanh::lean_is_exclusive(v_x_5917_)) as u8;
                    if v_isSharedCheck_5932_ == 0 {
                        v___x_5922_ = v_x_5917_;
                        v_isShared_5923_ = v_isSharedCheck_5932_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5920_);
                        crate::leanh::lean_inc(v_value_5919_);
                        crate::leanh::lean_inc(v_key_5918_);
                        crate::leanh::lean_dec(v_x_5917_);
                        v___x_5922_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_5922_, 2, v___x_5925_);
                        v___x_5927_ = v___x_5922_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5928_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5928_, 0, v_key_5918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5928_, 1, v_value_5919_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5928_, 2, v___x_5925_);
                        v___x_5927_ = v_reuseFailAlloc_5928_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_5919_);
                    crate::leanh::lean_dec(v_key_5918_);
                    if v_isShared_5923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5922_, 1, v_b_5916_);
                        crate::leanh::lean_ctor_set(v___x_5922_, 0, v_a_5915_);
                        v___x_5930_ = v___x_5922_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5931_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5915_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_b_5916_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5931_, 2, v_tail_5920_);
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
    mut v_a_5933_: *mut crate::leanh::LeanObject,
    mut v_x_5934_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5935_: u8 = 0;
    let mut v_key_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5934_) == 0 {
                    v___x_5935_ = 0;
                    return v___x_5935_;
                } else {
                    v_key_5936_ = crate::leanh::lean_ctor_get(v_x_5934_, 0);
                    v_tail_5937_ = crate::leanh::lean_ctor_get(v_x_5934_, 2);
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
    mut v_a_5940_: *mut crate::leanh::LeanObject,
    mut v_x_5941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5942_: u8 = 0;
    let mut v_r_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_5940_, v_x_5941_);
    crate::leanh::lean_dec(v_x_5941_);
    crate::leanh::lean_dec_ref(v_a_5940_);
    v_r_5943_ = crate::leanh::lean_box((v_res_5942_) as usize);
    return v_r_5943_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(
    mut v_m_5944_: *mut crate::leanh::LeanObject,
    mut v_a_5945_: *mut crate::leanh::LeanObject,
    mut v_b_5946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5951_: u8 = 0;
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: u8 = 0;
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: u8 = 0;
    let mut v_val_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5947_ = crate::leanh::lean_ctor_get(v_m_5944_, 0);
                v_buckets_5948_ = crate::leanh::lean_ctor_get(v_m_5944_, 1);
                v_isSharedCheck_5991_ = (!crate::leanh::lean_is_exclusive(v_m_5944_)) as u8;
                if v_isSharedCheck_5991_ == 0 {
                    v___x_5950_ = v_m_5944_;
                    v_isShared_5951_ = v_isSharedCheck_5991_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5948_);
                    crate::leanh::lean_inc(v_size_5947_);
                    crate::leanh::lean_dec(v_m_5944_);
                    v___x_5950_ = crate::leanh::lean_box(0);
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
                    v___x_5967_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5968_ = lean_nat_add(v_size_5947_, v___x_5967_);
                    crate::leanh::lean_dec(v_size_5947_);
                    crate::leanh::lean_inc(v_bkt_5965_);
                    v___x_5969_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5969_, 0, v_a_5945_);
                    crate::leanh::lean_ctor_set(v___x_5969_, 1, v_b_5946_);
                    crate::leanh::lean_ctor_set(v___x_5969_, 2, v_bkt_5965_);
                    v_buckets_x27_5970_ =
                        lean_array_uset(v_buckets_5948_, v___x_5964_, v___x_5969_);
                    v___x_5971_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5972_ = lean_nat_mul(v_size_x27_5968_, v___x_5971_);
                    v___x_5973_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5974_ = lean_nat_div(v___x_5972_, v___x_5973_);
                    crate::leanh::lean_dec(v___x_5972_);
                    v___x_5975_ = lean_array_get_size(v_buckets_x27_5970_);
                    v___x_5976_ = lean_nat_dec_le(v___x_5974_, v___x_5975_);
                    crate::leanh::lean_dec(v___x_5974_);
                    if v___x_5976_ == 0 {
                        v_val_5977_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_buckets_x27_5970_);
                        if v_isShared_5951_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5950_, 1, v_val_5977_);
                            crate::leanh::lean_ctor_set(v___x_5950_, 0, v_size_x27_5968_);
                            v___x_5979_ = v___x_5950_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5980_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5980_,
                                0,
                                v_size_x27_5968_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 1, v_val_5977_);
                            v___x_5979_ = v_reuseFailAlloc_5980_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5951_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5950_, 1, v_buckets_x27_5970_);
                            crate::leanh::lean_ctor_set(v___x_5950_, 0, v_size_x27_5968_);
                            v___x_5982_ = v___x_5950_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5983_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5983_,
                                0,
                                v_size_x27_5968_,
                            );
                            crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_inc(v_bkt_5965_);
                    v___x_5984_ = crate::leanh::lean_box(0);
                    v_buckets_x27_5985_ =
                        lean_array_uset(v_buckets_5948_, v___x_5964_, v___x_5984_);
                    v___x_5986_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_5945_, v_b_5946_, v_bkt_5965_);
                    v___x_5987_ = lean_array_uset(v_buckets_x27_5985_, v___x_5964_, v___x_5986_);
                    if v_isShared_5951_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5950_, 1, v___x_5987_);
                        v___x_5989_ = v___x_5950_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_size_5947_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5987_);
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
    mut v_a_5992_: *mut crate::leanh::LeanObject,
    mut v_e_5993_: *mut crate::leanh::LeanObject,
    mut v_a_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5996_ = lean_st_ref_take(v_a_5992_);
    v___x_5997_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_5996_, v_e_5993_, v_a_5994_);
    v___x_5998_ = lean_st_ref_set(v_a_5992_, v___x_5997_);
    v___x_5999_ = crate::leanh::lean_box(0);
    return v___x_5999_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(
    mut v_a_6000_: *mut crate::leanh::LeanObject,
    mut v_e_6001_: *mut crate::leanh::LeanObject,
    mut v_a_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6004_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_6000_, v_e_6001_, v_a_6002_);
    crate::leanh::lean_dec(v_a_6000_);
    return v_res_6004_;
}
pub unsafe fn _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6006_ = crate::leanh::lean_box(0);
    v_dummy_6007_ = l_Lean_Expr_sort___override(v___x_6006_);
    return v_dummy_6007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(
    mut v_pre_6008_: *mut crate::leanh::LeanObject,
    mut v_post_6009_: *mut crate::leanh::LeanObject,
    mut v_sz_6010_: usize,
    mut v_i_6011_: usize,
    mut v_bs_6012_: *mut crate::leanh::LeanObject,
    mut v___y_6013_: *mut crate::leanh::LeanObject,
    mut v___y_6014_: *mut crate::leanh::LeanObject,
    mut v___y_6015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: usize = 0;
    let mut v___x_6025_: usize = 0;
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6031_: u8 = 0;
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6017_ = lean_usize_dec_lt(v_i_6011_, v_sz_6010_);
                if v___x_6017_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_6009_);
                    crate::leanh::lean_dec_ref(v_pre_6008_);
                    v___x_6018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6018_, 0, v_bs_6012_);
                    return v___x_6018_;
                } else {
                    v_v_6019_ = lean_array_uget_borrowed(v_bs_6012_, v_i_6011_);
                    crate::leanh::lean_inc(v_v_6019_);
                    crate::leanh::lean_inc_ref(v_post_6009_);
                    crate::leanh::lean_inc_ref(v_pre_6008_);
                    v___x_6020_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6008_, v_post_6009_, v_v_6019_, v___y_6013_, v___y_6014_, v___y_6015_);
                    if crate::leanh::lean_obj_tag(v___x_6020_) == 0 {
                        v_a_6021_ = crate::leanh::lean_ctor_get(v___x_6020_, 0);
                        crate::leanh::lean_inc(v_a_6021_);
                        crate::leanh::lean_dec_ref_known(v___x_6020_, 1);
                        v___x_6022_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6023_ = lean_array_uset(v_bs_6012_, v_i_6011_, v___x_6022_);
                        v___x_6024_ = 1usize;
                        v___x_6025_ = lean_usize_add(v_i_6011_, v___x_6024_);
                        v___x_6026_ = lean_array_uset(v_bs_x27_6023_, v_i_6011_, v_a_6021_);
                        v_i_6011_ = v___x_6025_;
                        v_bs_6012_ = v___x_6026_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_6012_);
                        crate::leanh::lean_dec_ref(v_post_6009_);
                        crate::leanh::lean_dec_ref(v_pre_6008_);
                        v_a_6028_ = crate::leanh::lean_ctor_get(v___x_6020_, 0);
                        v_isSharedCheck_6035_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6020_)) as u8;
                        if v_isSharedCheck_6035_ == 0 {
                            v___x_6030_ = v___x_6020_;
                            v_isShared_6031_ = v_isSharedCheck_6035_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6028_);
                            crate::leanh::lean_dec(v___x_6020_);
                            v___x_6030_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_a_6028_);
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
    mut v_pre_6036_: *mut crate::leanh::LeanObject,
    mut v_post_6037_: *mut crate::leanh::LeanObject,
    mut v_x_6038_: *mut crate::leanh::LeanObject,
    mut v_x_6039_: *mut crate::leanh::LeanObject,
    mut v_x_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
    mut v___y_6042_: *mut crate::leanh::LeanObject,
    mut v___y_6043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6053_: usize = 0;
    let mut v___x_6054_: usize = 0;
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6062_: u8 = 0;
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6038_) == 5 {
                    v_fn_6045_ = crate::leanh::lean_ctor_get(v_x_6038_, 0);
                    crate::leanh::lean_inc_ref(v_fn_6045_);
                    v_arg_6046_ = crate::leanh::lean_ctor_get(v_x_6038_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6046_);
                    crate::leanh::lean_dec_ref_known(v_x_6038_, 2);
                    v___x_6047_ = lean_array_set(v_x_6039_, v_x_6040_, v_arg_6046_);
                    v___x_6048_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6049_ = lean_nat_sub(v_x_6040_, v___x_6048_);
                    crate::leanh::lean_dec(v_x_6040_);
                    v_x_6038_ = v_fn_6045_;
                    v_x_6039_ = v___x_6047_;
                    v_x_6040_ = v___x_6049_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_6040_);
                    crate::leanh::lean_inc_ref(v_post_6037_);
                    crate::leanh::lean_inc_ref(v_pre_6036_);
                    v___x_6051_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6036_, v_post_6037_, v_x_6038_, v___y_6041_, v___y_6042_, v___y_6043_);
                    if crate::leanh::lean_obj_tag(v___x_6051_) == 0 {
                        v_a_6052_ = crate::leanh::lean_ctor_get(v___x_6051_, 0);
                        crate::leanh::lean_inc(v_a_6052_);
                        crate::leanh::lean_dec_ref_known(v___x_6051_, 1);
                        v_sz_6053_ = lean_array_size(v_x_6039_);
                        v___x_6054_ = 0usize;
                        crate::leanh::lean_inc_ref(v_post_6037_);
                        crate::leanh::lean_inc_ref(v_pre_6036_);
                        v___x_6055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_6036_, v_post_6037_, v_sz_6053_, v___x_6054_, v_x_6039_, v___y_6041_, v___y_6042_, v___y_6043_);
                        if crate::leanh::lean_obj_tag(v___x_6055_) == 0 {
                            v_a_6056_ = crate::leanh::lean_ctor_get(v___x_6055_, 0);
                            crate::leanh::lean_inc(v_a_6056_);
                            crate::leanh::lean_dec_ref_known(v___x_6055_, 1);
                            v___x_6057_ = l_Lean_mkAppN(v_a_6052_, v_a_6056_);
                            crate::leanh::lean_dec(v_a_6056_);
                            v___x_6058_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6036_, v_post_6037_, v___x_6057_, v___y_6041_, v___y_6042_, v___y_6043_);
                            return v___x_6058_;
                        } else {
                            crate::leanh::lean_dec(v_a_6052_);
                            crate::leanh::lean_dec_ref(v_post_6037_);
                            crate::leanh::lean_dec_ref(v_pre_6036_);
                            v_a_6059_ = crate::leanh::lean_ctor_get(v___x_6055_, 0);
                            v_isSharedCheck_6066_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6055_)) as u8;
                            if v_isSharedCheck_6066_ == 0 {
                                v___x_6061_ = v___x_6055_;
                                v_isShared_6062_ = v_isSharedCheck_6066_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6059_);
                                crate::leanh::lean_dec(v___x_6055_);
                                v___x_6061_ = crate::leanh::lean_box(0);
                                v_isShared_6062_ = v_isSharedCheck_6066_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_6039_);
                        crate::leanh::lean_dec_ref(v_post_6037_);
                        crate::leanh::lean_dec_ref(v_pre_6036_);
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
                    v_reuseFailAlloc_6065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
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
    mut v___x_6067_: *mut crate::leanh::LeanObject,
    mut v_pre_6068_: *mut crate::leanh::LeanObject,
    mut v_e_6069_: *mut crate::leanh::LeanObject,
    mut v_post_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6081_: u8 = 0;
    let mut v___y_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6083_: u8 = 0;
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: usize = 0;
    let mut v___x_6087_: usize = 0;
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: u8 = 0;
    let mut v___y_6098_: u8 = 0;
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: u8 = 0;
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6107_: u8 = 0;
    let mut v___y_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6111_: u8 = 0;
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: u8 = 0;
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v___y_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6129_: u8 = 0;
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: usize = 0;
    let mut v___x_6135_: usize = 0;
    let mut v___x_6136_: u8 = 0;
    let mut v___x_6137_: usize = 0;
    let mut v___x_6138_: usize = 0;
    let mut v___x_6139_: u8 = 0;
    let mut v_binderName_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6143_: u8 = 0;
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: usize = 0;
    let mut v___x_6149_: usize = 0;
    let mut v___x_6150_: u8 = 0;
    let mut v___x_6151_: usize = 0;
    let mut v___x_6152_: usize = 0;
    let mut v___x_6153_: u8 = 0;
    let mut v_declName_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6158_: u8 = 0;
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: usize = 0;
    let mut v___x_6166_: usize = 0;
    let mut v___x_6167_: u8 = 0;
    let mut v___x_6168_: usize = 0;
    let mut v___x_6169_: usize = 0;
    let mut v___x_6170_: u8 = 0;
    let mut v_dummy_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: usize = 0;
    let mut v___x_6182_: usize = 0;
    let mut v___x_6183_: u8 = 0;
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: usize = 0;
    let mut v___x_6193_: usize = 0;
    let mut v___x_6194_: u8 = 0;
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_a_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6213_: u8 = 0;
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut v_a_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6221_: u8 = 0;
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6118_ = l_Lean_Core_checkSystem(v___x_6067_, v___y_6072_, v___y_6073_);
                if crate::leanh::lean_obj_tag(v___x_6118_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6118_, 1);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    crate::leanh::lean_inc(v___y_6073_);
                    crate::leanh::lean_inc_ref(v___y_6072_);
                    crate::leanh::lean_inc_ref(v_e_6069_);
                    v___x_6119_ = crate::leanh::lean_apply_4(
                        v_pre_6068_,
                        v_e_6069_,
                        v___y_6072_,
                        v___y_6073_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6119_) == 0 {
                        v_a_6120_ = crate::leanh::lean_ctor_get(v___x_6119_, 0);
                        v_isSharedCheck_6209_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6119_)) as u8;
                        if v_isSharedCheck_6209_ == 0 {
                            v___x_6122_ = v___x_6119_;
                            v_isShared_6123_ = v_isSharedCheck_6209_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6120_);
                            crate::leanh::lean_dec(v___x_6119_);
                            v___x_6122_ = crate::leanh::lean_box(0);
                            v_isShared_6123_ = v_isSharedCheck_6209_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_e_6069_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
                        v_a_6210_ = crate::leanh::lean_ctor_get(v___x_6119_, 0);
                        v_isSharedCheck_6217_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6119_)) as u8;
                        if v_isSharedCheck_6217_ == 0 {
                            v___x_6212_ = v___x_6119_;
                            v_isShared_6213_ = v_isSharedCheck_6217_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6210_);
                            crate::leanh::lean_dec(v___x_6119_);
                            v___x_6212_ = crate::leanh::lean_box(0);
                            v_isShared_6213_ = v_isSharedCheck_6217_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_6070_);
                    crate::leanh::lean_dec_ref(v_e_6069_);
                    crate::leanh::lean_dec_ref(v_pre_6068_);
                    v_a_6218_ = crate::leanh::lean_ctor_get(v___x_6118_, 0);
                    v_isSharedCheck_6225_ = (!crate::leanh::lean_is_exclusive(v___x_6118_)) as u8;
                    if v_isSharedCheck_6225_ == 0 {
                        v___x_6220_ = v___x_6118_;
                        v_isShared_6221_ = v_isSharedCheck_6225_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6218_);
                        crate::leanh::lean_dec(v___x_6118_);
                        v___x_6220_ = crate::leanh::lean_box(0);
                        v_isShared_6221_ = v_isSharedCheck_6225_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6083_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6079_);
                    crate::leanh::lean_dec_ref(v___y_6076_);
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
                    crate::leanh::lean_dec_ref(v___y_6076_);
                    v___x_6087_ = lean_ptr_addr(v___y_6078_);
                    v___x_6088_ = lean_usize_dec_eq(v___x_6086_, v___x_6087_);
                    if v___x_6088_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_6079_);
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
                        crate::leanh::lean_dec_ref(v___y_6082_);
                        crate::leanh::lean_dec_ref(v___y_6080_);
                        crate::leanh::lean_dec_ref(v___y_6078_);
                        crate::leanh::lean_dec(v___y_6077_);
                        v___x_6091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6079_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6091_;
                    }
                }
            }
            2 => {
                if v___y_6098_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6095_);
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
                        crate::leanh::lean_dec_ref(v___y_6095_);
                        v___x_6102_ = l_Lean_Expr_lam___override(
                            v___y_6093_,
                            v___y_6094_,
                            v___y_6096_,
                            v___y_6097_,
                        );
                        v___x_6103_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6102_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6103_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6096_);
                        crate::leanh::lean_dec_ref(v___y_6094_);
                        crate::leanh::lean_dec(v___y_6093_);
                        v___x_6104_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6095_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6104_;
                    }
                }
            }
            3 => {
                if v___y_6111_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6109_);
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
                        crate::leanh::lean_dec_ref(v___y_6109_);
                        v___x_6115_ = l_Lean_Expr_forallE___override(
                            v___y_6106_,
                            v___y_6108_,
                            v___y_6110_,
                            v___y_6107_,
                        );
                        v___x_6116_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6115_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6116_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6110_);
                        crate::leanh::lean_dec_ref(v___y_6108_);
                        crate::leanh::lean_dec(v___y_6106_);
                        v___x_6117_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6109_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6117_;
                    }
                }
            }
            4 => match crate::leanh::lean_obj_tag(v_a_6120_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_6070_);
                    crate::leanh::lean_dec_ref(v_e_6069_);
                    crate::leanh::lean_dec_ref(v_pre_6068_);
                    v_e_6199_ = crate::leanh::lean_ctor_get(v_a_6120_, 0);
                    crate::leanh::lean_inc_ref(v_e_6199_);
                    crate::leanh::lean_dec_ref_known(v_a_6120_, 1);
                    if v_isShared_6123_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6122_, 0, v_e_6199_);
                        v___x_6201_ = v___x_6122_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_e_6199_);
                        v___x_6201_ = v_reuseFailAlloc_6202_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6122_);
                    crate::leanh::lean_dec_ref(v_e_6069_);
                    v_e_6203_ = crate::leanh::lean_ctor_get(v_a_6120_, 0);
                    crate::leanh::lean_inc_ref(v_e_6203_);
                    crate::leanh::lean_dec_ref_known(v_a_6120_, 1);
                    crate::leanh::lean_inc_ref(v_post_6070_);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6204_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_e_6203_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if crate::leanh::lean_obj_tag(v___x_6204_) == 0 {
                        v_a_6205_ = crate::leanh::lean_ctor_get(v___x_6204_, 0);
                        crate::leanh::lean_inc(v_a_6205_);
                        crate::leanh::lean_dec_ref_known(v___x_6204_, 1);
                        v___x_6206_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v_a_6205_, v___y_6071_, v___y_6072_, v___y_6073_);
                        return v___x_6206_;
                    } else {
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6204_;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_6122_);
                    v_e_x3f_6207_ = crate::leanh::lean_ctor_get(v_a_6120_, 0);
                    crate::leanh::lean_inc(v_e_x3f_6207_);
                    crate::leanh::lean_dec_ref_known(v_a_6120_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_6207_) == 0 {
                        v___y_6125_ = v_e_6069_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6069_);
                        v_val_6208_ = crate::leanh::lean_ctor_get(v_e_x3f_6207_, 0);
                        crate::leanh::lean_inc(v_val_6208_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_6207_, 1);
                        v___y_6125_ = v_val_6208_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match crate::leanh::lean_obj_tag(v___y_6125_) {
                7 => {
                    v_binderName_6126_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    crate::leanh::lean_inc(v_binderName_6126_);
                    v_binderType_6127_ = crate::leanh::lean_ctor_get(v___y_6125_, 1);
                    v_body_6128_ = crate::leanh::lean_ctor_get(v___y_6125_, 2);
                    v_binderInfo_6129_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6125_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_6127_);
                    crate::leanh::lean_inc_ref(v_post_6070_);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6130_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_binderType_6127_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if crate::leanh::lean_obj_tag(v___x_6130_) == 0 {
                        v_a_6131_ = crate::leanh::lean_ctor_get(v___x_6130_, 0);
                        crate::leanh::lean_inc(v_a_6131_);
                        crate::leanh::lean_dec_ref_known(v___x_6130_, 1);
                        crate::leanh::lean_inc_ref(v_body_6128_);
                        crate::leanh::lean_inc_ref(v_post_6070_);
                        crate::leanh::lean_inc_ref(v_pre_6068_);
                        v___x_6132_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_body_6128_, v___y_6071_, v___y_6072_, v___y_6073_);
                        if crate::leanh::lean_obj_tag(v___x_6132_) == 0 {
                            v_a_6133_ = crate::leanh::lean_ctor_get(v___x_6132_, 0);
                            crate::leanh::lean_inc(v_a_6133_);
                            crate::leanh::lean_dec_ref_known(v___x_6132_, 1);
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
                            crate::leanh::lean_dec(v_a_6131_);
                            crate::leanh::lean_dec(v_binderName_6126_);
                            crate::leanh::lean_dec_ref_known(v___y_6125_, 3);
                            crate::leanh::lean_dec_ref(v_post_6070_);
                            crate::leanh::lean_dec_ref(v_pre_6068_);
                            return v___x_6132_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_6126_);
                        crate::leanh::lean_dec_ref_known(v___y_6125_, 3);
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6130_;
                    }
                }
                6 => {
                    v_binderName_6140_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    crate::leanh::lean_inc(v_binderName_6140_);
                    v_binderType_6141_ = crate::leanh::lean_ctor_get(v___y_6125_, 1);
                    v_body_6142_ = crate::leanh::lean_ctor_get(v___y_6125_, 2);
                    v_binderInfo_6143_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6125_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_6141_);
                    crate::leanh::lean_inc_ref(v_post_6070_);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6144_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_binderType_6141_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if crate::leanh::lean_obj_tag(v___x_6144_) == 0 {
                        v_a_6145_ = crate::leanh::lean_ctor_get(v___x_6144_, 0);
                        crate::leanh::lean_inc(v_a_6145_);
                        crate::leanh::lean_dec_ref_known(v___x_6144_, 1);
                        crate::leanh::lean_inc_ref(v_body_6142_);
                        crate::leanh::lean_inc_ref(v_post_6070_);
                        crate::leanh::lean_inc_ref(v_pre_6068_);
                        v___x_6146_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_body_6142_, v___y_6071_, v___y_6072_, v___y_6073_);
                        if crate::leanh::lean_obj_tag(v___x_6146_) == 0 {
                            v_a_6147_ = crate::leanh::lean_ctor_get(v___x_6146_, 0);
                            crate::leanh::lean_inc(v_a_6147_);
                            crate::leanh::lean_dec_ref_known(v___x_6146_, 1);
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
                            crate::leanh::lean_dec(v_a_6145_);
                            crate::leanh::lean_dec(v_binderName_6140_);
                            crate::leanh::lean_dec_ref_known(v___y_6125_, 3);
                            crate::leanh::lean_dec_ref(v_post_6070_);
                            crate::leanh::lean_dec_ref(v_pre_6068_);
                            return v___x_6146_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_binderName_6140_);
                        crate::leanh::lean_dec_ref_known(v___y_6125_, 3);
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6144_;
                    }
                }
                8 => {
                    v_declName_6154_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    crate::leanh::lean_inc(v_declName_6154_);
                    v_type_6155_ = crate::leanh::lean_ctor_get(v___y_6125_, 1);
                    v_value_6156_ = crate::leanh::lean_ctor_get(v___y_6125_, 2);
                    v_body_6157_ = crate::leanh::lean_ctor_get(v___y_6125_, 3);
                    crate::leanh::lean_inc_ref(v_body_6157_);
                    v_nondep_6158_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6125_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_6155_);
                    crate::leanh::lean_inc_ref(v_post_6070_);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6159_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_type_6155_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if crate::leanh::lean_obj_tag(v___x_6159_) == 0 {
                        v_a_6160_ = crate::leanh::lean_ctor_get(v___x_6159_, 0);
                        crate::leanh::lean_inc(v_a_6160_);
                        crate::leanh::lean_dec_ref_known(v___x_6159_, 1);
                        crate::leanh::lean_inc_ref(v_value_6156_);
                        crate::leanh::lean_inc_ref(v_post_6070_);
                        crate::leanh::lean_inc_ref(v_pre_6068_);
                        v___x_6161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_value_6156_, v___y_6071_, v___y_6072_, v___y_6073_);
                        if crate::leanh::lean_obj_tag(v___x_6161_) == 0 {
                            v_a_6162_ = crate::leanh::lean_ctor_get(v___x_6161_, 0);
                            crate::leanh::lean_inc(v_a_6162_);
                            crate::leanh::lean_dec_ref_known(v___x_6161_, 1);
                            crate::leanh::lean_inc_ref(v_body_6157_);
                            crate::leanh::lean_inc_ref(v_post_6070_);
                            crate::leanh::lean_inc_ref(v_pre_6068_);
                            v___x_6163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_body_6157_, v___y_6071_, v___y_6072_, v___y_6073_);
                            if crate::leanh::lean_obj_tag(v___x_6163_) == 0 {
                                v_a_6164_ = crate::leanh::lean_ctor_get(v___x_6163_, 0);
                                crate::leanh::lean_inc(v_a_6164_);
                                crate::leanh::lean_dec_ref_known(v___x_6163_, 1);
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
                                crate::leanh::lean_dec(v_a_6162_);
                                crate::leanh::lean_dec(v_a_6160_);
                                crate::leanh::lean_dec_ref(v_body_6157_);
                                crate::leanh::lean_dec(v_declName_6154_);
                                crate::leanh::lean_dec_ref_known(v___y_6125_, 4);
                                crate::leanh::lean_dec_ref(v_post_6070_);
                                crate::leanh::lean_dec_ref(v_pre_6068_);
                                return v___x_6163_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6160_);
                            crate::leanh::lean_dec_ref(v_body_6157_);
                            crate::leanh::lean_dec_ref_known(v___y_6125_, 4);
                            crate::leanh::lean_dec(v_declName_6154_);
                            crate::leanh::lean_dec_ref(v_post_6070_);
                            crate::leanh::lean_dec_ref(v_pre_6068_);
                            return v___x_6161_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_6157_);
                        crate::leanh::lean_dec_ref_known(v___y_6125_, 4);
                        crate::leanh::lean_dec(v_declName_6154_);
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6159_;
                    }
                }
                5 => {
                    v_dummy_6171_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_6172_ = l_Lean_Expr_getAppNumArgs(v___y_6125_);
                    crate::leanh::lean_inc(v_nargs_6172_);
                    v___x_6173_ = lean_mk_array(v_nargs_6172_, v_dummy_6171_);
                    v___x_6174_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6175_ = lean_nat_sub(v_nargs_6172_, v___x_6174_);
                    crate::leanh::lean_dec(v_nargs_6172_);
                    v___x_6176_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_6068_, v_post_6070_, v___y_6125_, v___x_6173_, v___x_6175_, v___y_6071_, v___y_6072_, v___y_6073_);
                    return v___x_6176_;
                }
                10 => {
                    v_data_6177_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    v_expr_6178_ = crate::leanh::lean_ctor_get(v___y_6125_, 1);
                    crate::leanh::lean_inc_ref(v_expr_6178_);
                    crate::leanh::lean_inc_ref(v_post_6070_);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6179_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_expr_6178_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if crate::leanh::lean_obj_tag(v___x_6179_) == 0 {
                        v_a_6180_ = crate::leanh::lean_ctor_get(v___x_6179_, 0);
                        crate::leanh::lean_inc(v_a_6180_);
                        crate::leanh::lean_dec_ref_known(v___x_6179_, 1);
                        v___x_6181_ = lean_ptr_addr(v_expr_6178_);
                        v___x_6182_ = lean_ptr_addr(v_a_6180_);
                        v___x_6183_ = lean_usize_dec_eq(v___x_6181_, v___x_6182_);
                        if v___x_6183_ == 0 {
                            crate::leanh::lean_inc(v_data_6177_);
                            crate::leanh::lean_dec_ref_known(v___y_6125_, 2);
                            v___x_6184_ = l_Lean_Expr_mdata___override(v_data_6177_, v_a_6180_);
                            v___x_6185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6184_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6185_;
                        } else {
                            crate::leanh::lean_dec(v_a_6180_);
                            v___x_6186_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6125_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6186_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6125_, 2);
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
                        return v___x_6179_;
                    }
                }
                11 => {
                    v_typeName_6187_ = crate::leanh::lean_ctor_get(v___y_6125_, 0);
                    v_idx_6188_ = crate::leanh::lean_ctor_get(v___y_6125_, 1);
                    v_struct_6189_ = crate::leanh::lean_ctor_get(v___y_6125_, 2);
                    crate::leanh::lean_inc_ref(v_struct_6189_);
                    crate::leanh::lean_inc_ref(v_post_6070_);
                    crate::leanh::lean_inc_ref(v_pre_6068_);
                    v___x_6190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6068_, v_post_6070_, v_struct_6189_, v___y_6071_, v___y_6072_, v___y_6073_);
                    if crate::leanh::lean_obj_tag(v___x_6190_) == 0 {
                        v_a_6191_ = crate::leanh::lean_ctor_get(v___x_6190_, 0);
                        crate::leanh::lean_inc(v_a_6191_);
                        crate::leanh::lean_dec_ref_known(v___x_6190_, 1);
                        v___x_6192_ = lean_ptr_addr(v_struct_6189_);
                        v___x_6193_ = lean_ptr_addr(v_a_6191_);
                        v___x_6194_ = lean_usize_dec_eq(v___x_6192_, v___x_6193_);
                        if v___x_6194_ == 0 {
                            crate::leanh::lean_inc(v_idx_6188_);
                            crate::leanh::lean_inc(v_typeName_6187_);
                            crate::leanh::lean_dec_ref_known(v___y_6125_, 3);
                            v___x_6195_ = l_Lean_Expr_proj___override(
                                v_typeName_6187_,
                                v_idx_6188_,
                                v_a_6191_,
                            );
                            v___x_6196_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___x_6195_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6196_;
                        } else {
                            crate::leanh::lean_dec(v_a_6191_);
                            v___x_6197_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6068_, v_post_6070_, v___y_6125_, v___y_6071_, v___y_6072_, v___y_6073_);
                            return v___x_6197_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6125_, 3);
                        crate::leanh::lean_dec_ref(v_post_6070_);
                        crate::leanh::lean_dec_ref(v_pre_6068_);
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
                    v_reuseFailAlloc_6216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
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
                    v_reuseFailAlloc_6224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6224_, 0, v_a_6218_);
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
    mut v___x_6226_: *mut crate::leanh::LeanObject,
    mut v_pre_6227_: *mut crate::leanh::LeanObject,
    mut v_e_6228_: *mut crate::leanh::LeanObject,
    mut v_post_6229_: *mut crate::leanh::LeanObject,
    mut v___y_6230_: *mut crate::leanh::LeanObject,
    mut v___y_6231_: *mut crate::leanh::LeanObject,
    mut v___y_6232_: *mut crate::leanh::LeanObject,
    mut v___y_6233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_6226_, v_pre_6227_, v_e_6228_, v_post_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
    crate::leanh::lean_dec(v___y_6232_);
    crate::leanh::lean_dec_ref(v___y_6231_);
    crate::leanh::lean_dec(v___y_6230_);
    return v_res_6234_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(
    mut v_pre_6235_: *mut crate::leanh::LeanObject,
    mut v_post_6236_: *mut crate::leanh::LeanObject,
    mut v_e_6237_: *mut crate::leanh::LeanObject,
    mut v_a_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6261_: u8 = 0;
    let mut v_unused_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6266_: u8 = 0;
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v_val_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6275_: u8 = 0;
    let mut v_a_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6279_: u8 = 0;
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6238_);
                v___x_6242_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_6242_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6242_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_6242_, 2, v_a_6238_);
                v___x_6243_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_6242_, v___y_6239_, v___y_6240_);
                if crate::leanh::lean_obj_tag(v___x_6243_) == 0 {
                    v_a_6244_ = crate::leanh::lean_ctor_get(v___x_6243_, 0);
                    v_isSharedCheck_6275_ = (!crate::leanh::lean_is_exclusive(v___x_6243_)) as u8;
                    if v_isSharedCheck_6275_ == 0 {
                        v___x_6246_ = v___x_6243_;
                        v_isShared_6247_ = v_isSharedCheck_6275_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6244_);
                        crate::leanh::lean_dec(v___x_6243_);
                        v___x_6246_ = crate::leanh::lean_box(0);
                        v_isShared_6247_ = v_isSharedCheck_6275_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6237_);
                    crate::leanh::lean_dec_ref(v_post_6236_);
                    crate::leanh::lean_dec_ref(v_pre_6235_);
                    v_a_6276_ = crate::leanh::lean_ctor_get(v___x_6243_, 0);
                    v_isSharedCheck_6283_ = (!crate::leanh::lean_is_exclusive(v___x_6243_)) as u8;
                    if v_isSharedCheck_6283_ == 0 {
                        v___x_6278_ = v___x_6243_;
                        v_isShared_6279_ = v_isSharedCheck_6283_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6276_);
                        crate::leanh::lean_dec(v___x_6243_);
                        v___x_6278_ = crate::leanh::lean_box(0);
                        v_isShared_6279_ = v_isSharedCheck_6283_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_6244_, v_e_6237_);
                crate::leanh::lean_dec(v_a_6244_);
                if crate::leanh::lean_obj_tag(v___x_6248_) == 0 {
                    crate::leanh::lean_del_object(v___x_6246_);
                    v___x_6249_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0;
                    crate::leanh::lean_inc_ref(v_e_6237_);
                    v___f_6250_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
                    crate::leanh::lean_closure_set(v___f_6250_, 0, v___x_6249_);
                    crate::leanh::lean_closure_set(v___f_6250_, 1, v_pre_6235_);
                    crate::leanh::lean_closure_set(v___f_6250_, 2, v_e_6237_);
                    crate::leanh::lean_closure_set(v___f_6250_, 3, v_post_6236_);
                    v___x_6251_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_6250_, v_a_6238_, v___y_6239_, v___y_6240_);
                    if crate::leanh::lean_obj_tag(v___x_6251_) == 0 {
                        v_a_6252_ = crate::leanh::lean_ctor_get(v___x_6251_, 0);
                        crate::leanh::lean_inc_n(v_a_6252_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6251_, 1);
                        crate::leanh::lean_inc(v_a_6238_);
                        v___f_6253_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_6253_, 0, v_a_6238_);
                        crate::leanh::lean_closure_set(v___f_6253_, 1, v_e_6237_);
                        crate::leanh::lean_closure_set(v___f_6253_, 2, v_a_6252_);
                        v___x_6254_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_6253_, v___y_6239_, v___y_6240_);
                        if crate::leanh::lean_obj_tag(v___x_6254_) == 0 {
                            v_isSharedCheck_6261_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6254_)) as u8;
                            if v_isSharedCheck_6261_ == 0 {
                                v_unused_6262_ = crate::leanh::lean_ctor_get(v___x_6254_, 0);
                                crate::leanh::lean_dec(v_unused_6262_);
                                v___x_6256_ = v___x_6254_;
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6254_);
                                v___x_6256_ = crate::leanh::lean_box(0);
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6252_);
                            v_a_6263_ = crate::leanh::lean_ctor_get(v___x_6254_, 0);
                            v_isSharedCheck_6270_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6254_)) as u8;
                            if v_isSharedCheck_6270_ == 0 {
                                v___x_6265_ = v___x_6254_;
                                v_isShared_6266_ = v_isSharedCheck_6270_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6263_);
                                crate::leanh::lean_dec(v___x_6254_);
                                v___x_6265_ = crate::leanh::lean_box(0);
                                v_isShared_6266_ = v_isSharedCheck_6270_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6237_);
                        return v___x_6251_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6237_);
                    crate::leanh::lean_dec_ref(v_post_6236_);
                    crate::leanh::lean_dec_ref(v_pre_6235_);
                    v_val_6271_ = crate::leanh::lean_ctor_get(v___x_6248_, 0);
                    crate::leanh::lean_inc(v_val_6271_);
                    crate::leanh::lean_dec_ref_known(v___x_6248_, 1);
                    if v_isShared_6247_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6246_, 0, v_val_6271_);
                        v___x_6273_ = v___x_6246_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_val_6271_);
                        v___x_6273_ = v_reuseFailAlloc_6274_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6257_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6256_, 0, v_a_6252_);
                    v___x_6259_ = v___x_6256_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6252_);
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
                    v_reuseFailAlloc_6269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_a_6263_);
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
                    v_reuseFailAlloc_6282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6282_, 0, v_a_6276_);
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
    mut v_pre_6284_: *mut crate::leanh::LeanObject,
    mut v_post_6285_: *mut crate::leanh::LeanObject,
    mut v_e_6286_: *mut crate::leanh::LeanObject,
    mut v_a_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
    mut v___y_6289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v_e_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_a_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_6285_);
                crate::leanh::lean_inc(v___y_6289_);
                crate::leanh::lean_inc_ref(v___y_6288_);
                crate::leanh::lean_inc_ref(v_e_6286_);
                v___x_6291_ = crate::leanh::lean_apply_4(
                    v_post_6285_,
                    v_e_6286_,
                    v___y_6288_,
                    v___y_6289_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6291_) == 0 {
                    v_a_6292_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6310_ = (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v___x_6294_ = v___x_6291_;
                        v_isShared_6295_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6292_);
                        crate::leanh::lean_dec(v___x_6291_);
                        v___x_6294_ = crate::leanh::lean_box(0);
                        v_isShared_6295_ = v_isSharedCheck_6310_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6286_);
                    crate::leanh::lean_dec_ref(v_post_6285_);
                    crate::leanh::lean_dec_ref(v_pre_6284_);
                    v_a_6311_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                    v_isSharedCheck_6318_ = (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                    if v_isSharedCheck_6318_ == 0 {
                        v___x_6313_ = v___x_6291_;
                        v_isShared_6314_ = v_isSharedCheck_6318_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6311_);
                        crate::leanh::lean_dec(v___x_6291_);
                        v___x_6313_ = crate::leanh::lean_box(0);
                        v_isShared_6314_ = v_isSharedCheck_6318_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_6292_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_6286_);
                    crate::leanh::lean_dec_ref(v_post_6285_);
                    crate::leanh::lean_dec_ref(v_pre_6284_);
                    v_e_6296_ = crate::leanh::lean_ctor_get(v_a_6292_, 0);
                    crate::leanh::lean_inc_ref(v_e_6296_);
                    crate::leanh::lean_dec_ref_known(v_a_6292_, 1);
                    if v_isShared_6295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6294_, 0, v_e_6296_);
                        v___x_6298_ = v___x_6294_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_e_6296_);
                        v___x_6298_ = v_reuseFailAlloc_6299_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6294_);
                    crate::leanh::lean_dec_ref(v_e_6286_);
                    v_e_6300_ = crate::leanh::lean_ctor_get(v_a_6292_, 0);
                    crate::leanh::lean_inc_ref(v_e_6300_);
                    crate::leanh::lean_dec_ref_known(v_a_6292_, 1);
                    v___x_6301_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6284_, v_post_6285_, v_e_6300_, v_a_6287_, v___y_6288_, v___y_6289_);
                    return v___x_6301_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_6285_);
                    crate::leanh::lean_dec_ref(v_pre_6284_);
                    v_e_x3f_6302_ = crate::leanh::lean_ctor_get(v_a_6292_, 0);
                    crate::leanh::lean_inc(v_e_x3f_6302_);
                    crate::leanh::lean_dec_ref_known(v_a_6292_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_6302_) == 0 {
                        if v_isShared_6295_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6294_, 0, v_e_6286_);
                            v___x_6304_ = v___x_6294_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6305_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_e_6286_);
                            v___x_6304_ = v_reuseFailAlloc_6305_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6286_);
                        v_val_6306_ = crate::leanh::lean_ctor_get(v_e_x3f_6302_, 0);
                        crate::leanh::lean_inc(v_val_6306_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_6302_, 1);
                        if v_isShared_6295_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6294_, 0, v_val_6306_);
                            v___x_6308_ = v___x_6294_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6309_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_val_6306_);
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
                    v_reuseFailAlloc_6317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_a_6311_);
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
    mut v_pre_6319_: *mut crate::leanh::LeanObject,
    mut v_post_6320_: *mut crate::leanh::LeanObject,
    mut v_e_6321_: *mut crate::leanh::LeanObject,
    mut v_a_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6326_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_6319_, v_post_6320_, v_e_6321_, v_a_6322_, v___y_6323_, v___y_6324_);
    crate::leanh::lean_dec(v___y_6324_);
    crate::leanh::lean_dec_ref(v___y_6323_);
    crate::leanh::lean_dec(v_a_6322_);
    return v_res_6326_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(
    mut v_pre_6327_: *mut crate::leanh::LeanObject,
    mut v_post_6328_: *mut crate::leanh::LeanObject,
    mut v_sz_6329_: *mut crate::leanh::LeanObject,
    mut v_i_6330_: *mut crate::leanh::LeanObject,
    mut v_bs_6331_: *mut crate::leanh::LeanObject,
    mut v___y_6332_: *mut crate::leanh::LeanObject,
    mut v___y_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6336_: usize = 0;
    let mut v_i_boxed_6337_: usize = 0;
    let mut v_res_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6336_ = crate::leanh::lean_unbox_usize(v_sz_6329_);
    crate::leanh::lean_dec(v_sz_6329_);
    v_i_boxed_6337_ = crate::leanh::lean_unbox_usize(v_i_6330_);
    crate::leanh::lean_dec(v_i_6330_);
    v_res_6338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_6327_, v_post_6328_, v_sz_boxed_6336_, v_i_boxed_6337_, v_bs_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
    crate::leanh::lean_dec(v___y_6334_);
    crate::leanh::lean_dec_ref(v___y_6333_);
    crate::leanh::lean_dec(v___y_6332_);
    return v_res_6338_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(
    mut v_pre_6339_: *mut crate::leanh::LeanObject,
    mut v_post_6340_: *mut crate::leanh::LeanObject,
    mut v_x_6341_: *mut crate::leanh::LeanObject,
    mut v_x_6342_: *mut crate::leanh::LeanObject,
    mut v_x_6343_: *mut crate::leanh::LeanObject,
    mut v___y_6344_: *mut crate::leanh::LeanObject,
    mut v___y_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
    mut v___y_6347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6348_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_6339_, v_post_6340_, v_x_6341_, v_x_6342_, v_x_6343_, v___y_6344_, v___y_6345_, v___y_6346_);
    crate::leanh::lean_dec(v___y_6346_);
    crate::leanh::lean_dec_ref(v___y_6345_);
    crate::leanh::lean_dec(v___y_6344_);
    return v_res_6348_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(
    mut v_pre_6349_: *mut crate::leanh::LeanObject,
    mut v_post_6350_: *mut crate::leanh::LeanObject,
    mut v_e_6351_: *mut crate::leanh::LeanObject,
    mut v_a_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
    mut v___y_6355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6356_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6349_, v_post_6350_, v_e_6351_, v_a_6352_, v___y_6353_, v___y_6354_);
    crate::leanh::lean_dec(v___y_6354_);
    crate::leanh::lean_dec_ref(v___y_6353_);
    crate::leanh::lean_dec(v_a_6352_);
    return v_res_6356_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6357_ = crate::leanh::lean_box(0);
    v___x_6358_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_6359_ = lean_mk_array(v___x_6358_, v___x_6357_);
    return v___x_6359_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
    v___x_6361_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6362_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6362_, 0, v___x_6361_);
    crate::leanh::lean_ctor_set(v___x_6362_, 1, v___x_6360_);
    return v___x_6362_;
}
pub unsafe fn _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6363_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
    v___x_6364_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_6364_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6364_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_6364_, 2, v___x_6363_);
    return v___x_6364_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(
    mut v_input_6365_: *mut crate::leanh::LeanObject,
    mut v_pre_6366_: *mut crate::leanh::LeanObject,
    mut v_post_6367_: *mut crate::leanh::LeanObject,
    mut v___y_6368_: *mut crate::leanh::LeanObject,
    mut v___y_6369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6380_: u8 = 0;
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6384_: u8 = 0;
    let mut v_unused_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6371_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
                v___x_6372_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(crate::leanh::lean_box(0), v___x_6371_, v___y_6368_, v___y_6369_);
                v_a_6373_ = crate::leanh::lean_ctor_get(v___x_6372_, 0);
                crate::leanh::lean_inc(v_a_6373_);
                crate::leanh::lean_dec_ref(v___x_6372_);
                v___x_6374_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_6366_, v_post_6367_, v_input_6365_, v_a_6373_, v___y_6368_, v___y_6369_);
                if crate::leanh::lean_obj_tag(v___x_6374_) == 0 {
                    v_a_6375_ = crate::leanh::lean_ctor_get(v___x_6374_, 0);
                    crate::leanh::lean_inc(v_a_6375_);
                    crate::leanh::lean_dec_ref_known(v___x_6374_, 1);
                    v___x_6376_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_6376_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_6376_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_6376_, 2, v_a_6373_);
                    v___x_6377_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(crate::leanh::lean_box(0), v___x_6376_, v___y_6368_, v___y_6369_);
                    v_isSharedCheck_6384_ = (!crate::leanh::lean_is_exclusive(v___x_6377_)) as u8;
                    if v_isSharedCheck_6384_ == 0 {
                        v_unused_6385_ = crate::leanh::lean_ctor_get(v___x_6377_, 0);
                        crate::leanh::lean_dec(v_unused_6385_);
                        v___x_6379_ = v___x_6377_;
                        v_isShared_6380_ = v_isSharedCheck_6384_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6377_);
                        v___x_6379_ = crate::leanh::lean_box(0);
                        v_isShared_6380_ = v_isSharedCheck_6384_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6373_);
                    return v___x_6374_;
                }
            }
            1 => {
                if v_isShared_6380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6379_, 0, v_a_6375_);
                    v___x_6382_ = v___x_6379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_a_6375_);
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
    mut v_input_6386_: *mut crate::leanh::LeanObject,
    mut v_pre_6387_: *mut crate::leanh::LeanObject,
    mut v_post_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6392_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(
        v_input_6386_,
        v_pre_6387_,
        v_post_6388_,
        v___y_6389_,
        v___y_6390_,
    );
    crate::leanh::lean_dec(v___y_6390_);
    crate::leanh::lean_dec_ref(v___y_6389_);
    return v_res_6392_;
}
pub unsafe fn l_Lean_Meta_Grind_eraseIrrelevantMData(
    mut v_e_6396_: *mut crate::leanh::LeanObject,
    mut v_a_6397_: *mut crate::leanh::LeanObject,
    mut v_a_6398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6400_ = l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0;
    v___x_6401_ = lean_find_expr(v___f_6400_, v_e_6396_);
    if crate::leanh::lean_obj_tag(v___x_6401_) == 0 {
        let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6402_, 0, v_e_6396_);
        return v___x_6402_;
    } else {
        let mut v_pre_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_6401_, 1);
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
    mut v_e_6406_: *mut crate::leanh::LeanObject,
    mut v_a_6407_: *mut crate::leanh::LeanObject,
    mut v_a_6408_: *mut crate::leanh::LeanObject,
    mut v_a_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6410_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_6406_, v_a_6407_, v_a_6408_);
    crate::leanh::lean_dec(v_a_6408_);
    crate::leanh::lean_dec_ref(v_a_6407_);
    return v_res_6410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(
    mut v_00_u03b2_6411_: *mut crate::leanh::LeanObject,
    mut v_m_6412_: *mut crate::leanh::LeanObject,
    mut v_a_6413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_6412_, v_a_6413_);
    return v___x_6414_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_6415_: *mut crate::leanh::LeanObject,
    mut v_m_6416_: *mut crate::leanh::LeanObject,
    mut v_a_6417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_6415_, v_m_6416_, v_a_6417_);
    crate::leanh::lean_dec_ref(v_a_6417_);
    crate::leanh::lean_dec_ref(v_m_6416_);
    return v_res_6418_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(
    mut v_00_u03b1_6419_: *mut crate::leanh::LeanObject,
    mut v_ref_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6424_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_6420_);
    return v___x_6424_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(
    mut v_00_u03b1_6425_: *mut crate::leanh::LeanObject,
    mut v_ref_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_6425_, v_ref_6426_, v___y_6427_, v___y_6428_);
    crate::leanh::lean_dec(v___y_6428_);
    crate::leanh::lean_dec_ref(v___y_6427_);
    return v_res_6430_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(
    mut v_00_u03b1_6431_: *mut crate::leanh::LeanObject,
    mut v___y_6432_: *mut crate::leanh::LeanObject,
    mut v___y_6433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6435_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
    return v___x_6435_;
}
pub unsafe fn l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___boxed(
    mut v_00_u03b1_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6440_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8(v_00_u03b1_6436_, v___y_6437_, v___y_6438_);
    crate::leanh::lean_dec(v___y_6438_);
    crate::leanh::lean_dec_ref(v___y_6437_);
    return v_res_6440_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(
    mut v_00_u03b1_6441_: *mut crate::leanh::LeanObject,
    mut v_x_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6447_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
    return v___x_6447_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(
    mut v_00_u03b1_6448_: *mut crate::leanh::LeanObject,
    mut v_x_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6454_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_6448_, v_x_6449_, v___y_6450_, v___y_6451_, v___y_6452_);
    crate::leanh::lean_dec(v___y_6452_);
    crate::leanh::lean_dec_ref(v___y_6451_);
    crate::leanh::lean_dec(v___y_6450_);
    return v_res_6454_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(
    mut v_00_u03b2_6455_: *mut crate::leanh::LeanObject,
    mut v_m_6456_: *mut crate::leanh::LeanObject,
    mut v_a_6457_: *mut crate::leanh::LeanObject,
    mut v_b_6458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_6456_, v_a_6457_, v_b_6458_);
    return v___x_6459_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(
    mut v_00_u03b2_6460_: *mut crate::leanh::LeanObject,
    mut v_a_6461_: *mut crate::leanh::LeanObject,
    mut v_x_6462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6463_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_6461_, v_x_6462_);
    return v___x_6463_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(
    mut v_00_u03b2_6464_: *mut crate::leanh::LeanObject,
    mut v_a_6465_: *mut crate::leanh::LeanObject,
    mut v_x_6466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6467_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_6464_, v_a_6465_, v_x_6466_);
    crate::leanh::lean_dec(v_x_6466_);
    crate::leanh::lean_dec_ref(v_a_6465_);
    return v_res_6467_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(
    mut v_00_u03b2_6468_: *mut crate::leanh::LeanObject,
    mut v_a_6469_: *mut crate::leanh::LeanObject,
    mut v_x_6470_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6471_: u8 = 0;
    v___x_6471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_a_6469_, v_x_6470_);
    return v___x_6471_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___boxed(
    mut v_00_u03b2_6472_: *mut crate::leanh::LeanObject,
    mut v_a_6473_: *mut crate::leanh::LeanObject,
    mut v_x_6474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6475_: u8 = 0;
    let mut v_r_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6475_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(v_00_u03b2_6472_, v_a_6473_, v_x_6474_);
    crate::leanh::lean_dec(v_x_6474_);
    crate::leanh::lean_dec_ref(v_a_6473_);
    v_r_6476_ = crate::leanh::lean_box((v_res_6475_) as usize);
    return v_r_6476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(
    mut v_00_u03b2_6477_: *mut crate::leanh::LeanObject,
    mut v_data_6478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_data_6478_);
    return v___x_6479_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12(
    mut v_00_u03b2_6480_: *mut crate::leanh::LeanObject,
    mut v_a_6481_: *mut crate::leanh::LeanObject,
    mut v_b_6482_: *mut crate::leanh::LeanObject,
    mut v_x_6483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6484_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__12___redArg(v_a_6481_, v_b_6482_, v_x_6483_);
    return v___x_6484_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12(
    mut v_00_u03b2_6485_: *mut crate::leanh::LeanObject,
    mut v_i_6486_: *mut crate::leanh::LeanObject,
    mut v_source_6487_: *mut crate::leanh::LeanObject,
    mut v_target_6488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12___redArg(v_i_6486_, v_source_6487_, v_target_6488_);
    return v___x_6489_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13(
    mut v_00_u03b2_6490_: *mut crate::leanh::LeanObject,
    mut v_x_6491_: *mut crate::leanh::LeanObject,
    mut v_x_6492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11_spec__12_spec__13___redArg(v_x_6491_, v_x_6492_);
    return v___x_6493_;
}
pub unsafe fn l_Lean_Meta_Grind_foldProjs(
    mut v_e_6494_: *mut crate::leanh::LeanObject,
    mut v_a_6495_: *mut crate::leanh::LeanObject,
    mut v_a_6496_: *mut crate::leanh::LeanObject,
    mut v_a_6497_: *mut crate::leanh::LeanObject,
    mut v_a_6498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6500_ = l_Lean_Meta_Sym_foldProjs(v_e_6494_, v_a_6495_, v_a_6496_, v_a_6497_, v_a_6498_);
    return v___x_6500_;
}
pub unsafe fn l_Lean_Meta_Grind_foldProjs___boxed(
    mut v_e_6501_: *mut crate::leanh::LeanObject,
    mut v_a_6502_: *mut crate::leanh::LeanObject,
    mut v_a_6503_: *mut crate::leanh::LeanObject,
    mut v_a_6504_: *mut crate::leanh::LeanObject,
    mut v_a_6505_: *mut crate::leanh::LeanObject,
    mut v_a_6506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6507_ =
        l_Lean_Meta_Grind_foldProjs(v_e_6501_, v_a_6502_, v_a_6503_, v_a_6504_, v_a_6505_);
    crate::leanh::lean_dec(v_a_6505_);
    crate::leanh::lean_dec_ref(v_a_6504_);
    crate::leanh::lean_dec(v_a_6503_);
    crate::leanh::lean_dec_ref(v_a_6502_);
    return v_res_6507_;
}
pub unsafe fn l_Lean_Meta_Grind_normalize___boxed(
    mut v_e_6515_: *mut crate::leanh::LeanObject,
    mut v_config_6516_: *mut crate::leanh::LeanObject,
    mut v_a_6517_: *mut crate::leanh::LeanObject,
    mut v_a_6518_: *mut crate::leanh::LeanObject,
    mut v_a_6519_: *mut crate::leanh::LeanObject,
    mut v_a_6520_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_6521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6530_ = crate::leanh::lean_box(0);
    v___x_6531_ = l_Lean_Meta_Grind_markAsMatchCond___closed__3;
    v___x_6532_ = l_Lean_mkConst(v___x_6531_, v___x_6530_);
    return v___x_6532_;
}
pub unsafe fn l_Lean_Meta_Grind_markAsMatchCond(
    mut v_e_6533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6534_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsMatchCond___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsMatchCond___closed__4_once),
        _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4,
    );
    v___x_6535_ = l_Lean_Expr_app___override(v___x_6534_, v_e_6533_);
    return v___x_6535_;
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCond(mut v_e_6536_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: u8 = 0;
    v___x_6537_ = l_Lean_Meta_Grind_markAsMatchCond___closed__3;
    v___x_6538_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_6539_ = l_Lean_Expr_isAppOfArity(v_e_6536_, v___x_6537_, v___x_6538_);
    return v___x_6539_;
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCond___boxed(
    mut v_e_6540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6541_: u8 = 0;
    let mut v_r_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6541_ = l_Lean_Meta_Grind_isMatchCond(v_e_6540_);
    crate::leanh::lean_dec_ref(v_e_6540_);
    v_r_6542_ = crate::leanh::lean_box((v_res_6541_) as usize);
    return v_r_6542_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6548_ = crate::leanh::lean_box(0);
    v___x_6549_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
    v___x_6550_ = l_Lean_mkConst(v___x_6549_, v___x_6548_);
    return v___x_6550_;
}
pub unsafe fn l_Lean_Meta_Grind_markAsPreMatchCond(
    mut v_e_6551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once),
        _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2,
    );
    v___x_6553_ = l_Lean_Expr_app___override(v___x_6552_, v_e_6551_);
    return v___x_6553_;
}
pub unsafe fn l_Lean_Meta_Grind_isPreMatchCond(mut v_e_6554_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: u8 = 0;
    v___x_6555_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
    v___x_6556_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_6557_ = l_Lean_Expr_isAppOfArity(v_e_6554_, v___x_6555_, v___x_6556_);
    return v___x_6557_;
}
pub unsafe fn l_Lean_Meta_Grind_isPreMatchCond___boxed(
    mut v_e_6558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6559_: u8 = 0;
    let mut v_r_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6559_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_6558_);
    crate::leanh::lean_dec_ref(v_e_6558_);
    v_r_6560_ = crate::leanh::lean_box((v_res_6559_) as usize);
    return v_r_6560_;
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond___redArg(
    mut v_e_6563_: *mut crate::leanh::LeanObject,
    mut v_a_6564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6570_: u8 = 0;
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: u8 = 0;
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6583_: u8 = 0;
    let mut v_a_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_6563_);
                v___x_6566_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6563_, v_a_6564_);
                if crate::leanh::lean_obj_tag(v___x_6566_) == 0 {
                    v_a_6567_ = crate::leanh::lean_ctor_get(v___x_6566_, 0);
                    v_isSharedCheck_6583_ = (!crate::leanh::lean_is_exclusive(v___x_6566_)) as u8;
                    if v_isSharedCheck_6583_ == 0 {
                        v___x_6569_ = v___x_6566_;
                        v_isShared_6570_ = v_isSharedCheck_6583_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6567_);
                        crate::leanh::lean_dec(v___x_6566_);
                        v___x_6569_ = crate::leanh::lean_box(0);
                        v_isShared_6570_ = v_isSharedCheck_6583_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6563_);
                    v_a_6584_ = crate::leanh::lean_ctor_get(v___x_6566_, 0);
                    v_isSharedCheck_6591_ = (!crate::leanh::lean_is_exclusive(v___x_6566_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6566_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6584_);
                        crate::leanh::lean_dec(v___x_6566_);
                        v___x_6586_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec_ref(v___x_6576_);
                    crate::leanh::lean_dec_ref(v_e_6563_);
                    state = 2;
                    continue;
                } else {
                    v___x_6578_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6576_);
                    v___x_6579_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
                    v___x_6580_ = l_Lean_Expr_isConstOf(v___x_6578_, v___x_6579_);
                    crate::leanh::lean_dec_ref(v___x_6578_);
                    if v___x_6580_ == 0 {
                        crate::leanh::lean_dec_ref(v_e_6563_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_6569_);
                        v___x_6581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6581_, 0, v_e_6563_);
                        v___x_6582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6582_, 0, v___x_6581_);
                        return v___x_6582_;
                    }
                }
            }
            2 => {
                v___x_6572_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg___closed__0;
                if v_isShared_6570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6569_, 0, v___x_6572_);
                    v___x_6574_ = v___x_6569_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6572_);
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
                    v_reuseFailAlloc_6590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
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
    mut v_e_6592_: *mut crate::leanh::LeanObject,
    mut v_a_6593_: *mut crate::leanh::LeanObject,
    mut v_a_6594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6595_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_6592_, v_a_6593_);
    crate::leanh::lean_dec(v_a_6593_);
    return v_res_6595_;
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond(
    mut v_e_6596_: *mut crate::leanh::LeanObject,
    mut v_a_6597_: *mut crate::leanh::LeanObject,
    mut v_a_6598_: *mut crate::leanh::LeanObject,
    mut v_a_6599_: *mut crate::leanh::LeanObject,
    mut v_a_6600_: *mut crate::leanh::LeanObject,
    mut v_a_6601_: *mut crate::leanh::LeanObject,
    mut v_a_6602_: *mut crate::leanh::LeanObject,
    mut v_a_6603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6605_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_6596_, v_a_6601_);
    return v___x_6605_;
}
pub unsafe fn l_Lean_Meta_Grind_reducePreMatchCond___boxed(
    mut v_e_6606_: *mut crate::leanh::LeanObject,
    mut v_a_6607_: *mut crate::leanh::LeanObject,
    mut v_a_6608_: *mut crate::leanh::LeanObject,
    mut v_a_6609_: *mut crate::leanh::LeanObject,
    mut v_a_6610_: *mut crate::leanh::LeanObject,
    mut v_a_6611_: *mut crate::leanh::LeanObject,
    mut v_a_6612_: *mut crate::leanh::LeanObject,
    mut v_a_6613_: *mut crate::leanh::LeanObject,
    mut v_a_6614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6615_ = l_Lean_Meta_Grind_reducePreMatchCond(
        v_e_6606_, v_a_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_, v_a_6612_, v_a_6613_,
    );
    crate::leanh::lean_dec(v_a_6613_);
    crate::leanh::lean_dec_ref(v_a_6612_);
    crate::leanh::lean_dec(v_a_6611_);
    crate::leanh::lean_dec_ref(v_a_6610_);
    crate::leanh::lean_dec(v_a_6609_);
    crate::leanh::lean_dec_ref(v_a_6608_);
    crate::leanh::lean_dec(v_a_6607_);
    return v_res_6615_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6633_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_;
    v___x_6634_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_;
    v___x_6635_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_reducePreMatchCond___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6636_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_6633_, v___x_6634_, v___x_6635_);
    return v___x_6636_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(
    mut v_a_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6638_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
    return v_res_6638_;
}
pub unsafe fn l_Lean_Meta_Grind_addPreMatchCondSimproc(
    mut v_s_6639_: *mut crate::leanh::LeanObject,
    mut v_a_6640_: *mut crate::leanh::LeanObject,
    mut v_a_6641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: u8 = 0;
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6643_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_;
    v___x_6644_ = 0;
    v___x_6645_ =
        l_Lean_Meta_Simp_Simprocs_add(v_s_6639_, v___x_6643_, v___x_6644_, v_a_6640_, v_a_6641_);
    return v___x_6645_;
}
pub unsafe fn l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(
    mut v_s_6646_: *mut crate::leanh::LeanObject,
    mut v_a_6647_: *mut crate::leanh::LeanObject,
    mut v_a_6648_: *mut crate::leanh::LeanObject,
    mut v_a_6649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6650_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_6646_, v_a_6647_, v_a_6648_);
    crate::leanh::lean_dec(v_a_6648_);
    crate::leanh::lean_dec_ref(v_a_6647_);
    return v_res_6650_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__0(
    mut v_e_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: u8 = 0;
    let mut v_arg_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: u8 = 0;
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_6651_);
                v___x_6661_ = l_Lean_Expr_cleanupAnnotations(v_e_6651_);
                v___x_6662_ = l_Lean_Expr_isApp(v___x_6661_);
                if v___x_6662_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_6661_);
                    state = 1;
                    continue;
                } else {
                    v_arg_6663_ = crate::leanh::lean_ctor_get(v___x_6661_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6663_);
                    v___x_6664_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6661_);
                    v___x_6665_ = l_Lean_Meta_Grind_markAsPreMatchCond___closed__1;
                    v___x_6666_ = l_Lean_Expr_isConstOf(v___x_6664_, v___x_6665_);
                    crate::leanh::lean_dec_ref(v___x_6664_);
                    if v___x_6666_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_6663_);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6651_);
                        v___x_6667_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_6663_);
                        v___x_6668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6668_, 0, v___x_6667_);
                        v___x_6669_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6669_, 0, v___x_6668_);
                        v___x_6670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6670_, 0, v___x_6669_);
                        return v___x_6670_;
                    }
                }
            }
            1 => {
                v___x_6658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6658_, 0, v_e_6651_);
                v___x_6659_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6659_, 0, v___x_6658_);
                v___x_6660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6660_, 0, v___x_6659_);
                return v___x_6660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(
    mut v_e_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
    mut v___y_6673_: *mut crate::leanh::LeanObject,
    mut v___y_6674_: *mut crate::leanh::LeanObject,
    mut v___y_6675_: *mut crate::leanh::LeanObject,
    mut v___y_6676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6677_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(
        v_e_6671_,
        v___y_6672_,
        v___y_6673_,
        v___y_6674_,
        v___y_6675_,
    );
    crate::leanh::lean_dec(v___y_6675_);
    crate::leanh::lean_dec_ref(v___y_6674_);
    crate::leanh::lean_dec(v___y_6673_);
    crate::leanh::lean_dec_ref(v___y_6672_);
    return v_res_6677_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__1(
    mut v_e_6678_: *mut crate::leanh::LeanObject,
    mut v___y_6679_: *mut crate::leanh::LeanObject,
    mut v___y_6680_: *mut crate::leanh::LeanObject,
    mut v___y_6681_: *mut crate::leanh::LeanObject,
    mut v___y_6682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6684_, 0, v_e_6678_);
    v___x_6685_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6685_, 0, v___x_6684_);
    return v___x_6685_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(
    mut v_e_6686_: *mut crate::leanh::LeanObject,
    mut v___y_6687_: *mut crate::leanh::LeanObject,
    mut v___y_6688_: *mut crate::leanh::LeanObject,
    mut v___y_6689_: *mut crate::leanh::LeanObject,
    mut v___y_6690_: *mut crate::leanh::LeanObject,
    mut v___y_6691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6692_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(
        v_e_6686_,
        v___y_6687_,
        v___y_6688_,
        v___y_6689_,
        v___y_6690_,
    );
    crate::leanh::lean_dec(v___y_6690_);
    crate::leanh::lean_dec_ref(v___y_6689_);
    crate::leanh::lean_dec(v___y_6688_);
    crate::leanh::lean_dec_ref(v___y_6687_);
    return v_res_6692_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(
    mut v_00_u03b1_6693_: *mut crate::leanh::LeanObject,
    mut v_x_6694_: *mut crate::leanh::LeanObject,
    mut v___y_6695_: *mut crate::leanh::LeanObject,
    mut v___y_6696_: *mut crate::leanh::LeanObject,
    mut v___y_6697_: *mut crate::leanh::LeanObject,
    mut v___y_6698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6700_ = crate::leanh::lean_apply_1(v_x_6694_, crate::leanh::lean_box(0));
    v___x_6701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
    return v___x_6701_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0___boxed(
    mut v_00_u03b1_6702_: *mut crate::leanh::LeanObject,
    mut v_x_6703_: *mut crate::leanh::LeanObject,
    mut v___y_6704_: *mut crate::leanh::LeanObject,
    mut v___y_6705_: *mut crate::leanh::LeanObject,
    mut v___y_6706_: *mut crate::leanh::LeanObject,
    mut v___y_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6709_ =
        l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(
            v_00_u03b1_6702_,
            v_x_6703_,
            v___y_6704_,
            v___y_6705_,
            v___y_6706_,
            v___y_6707_,
        );
    crate::leanh::lean_dec(v___y_6707_);
    crate::leanh::lean_dec_ref(v___y_6706_);
    crate::leanh::lean_dec(v___y_6705_);
    crate::leanh::lean_dec_ref(v___y_6704_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(
    mut v_x_6710_: *mut crate::leanh::LeanObject,
    mut v___y_6711_: *mut crate::leanh::LeanObject,
    mut v___y_6712_: *mut crate::leanh::LeanObject,
    mut v___y_6713_: *mut crate::leanh::LeanObject,
    mut v___y_6714_: *mut crate::leanh::LeanObject,
    mut v___y_6715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6722_: u8 = 0;
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6726_: u8 = 0;
    let mut v___y_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6738_: u8 = 0;
    let mut v___y_6739_: u8 = 0;
    let mut v___y_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6760_: u8 = 0;
    let mut v_cancelTk_x3f_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6762_: u8 = 0;
    let mut v_inheritedTraceOptions_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: u8 = 0;
    let mut v___x_6767_: u8 = 0;
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: u8 = 0;
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6775_: u8 = 0;
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6748_ = crate::leanh::lean_ctor_get(v___y_6714_, 0);
                v_fileMap_6749_ = crate::leanh::lean_ctor_get(v___y_6714_, 1);
                v_options_6750_ = crate::leanh::lean_ctor_get(v___y_6714_, 2);
                v_currRecDepth_6751_ = crate::leanh::lean_ctor_get(v___y_6714_, 3);
                v_maxRecDepth_6752_ = crate::leanh::lean_ctor_get(v___y_6714_, 4);
                v_ref_6753_ = crate::leanh::lean_ctor_get(v___y_6714_, 5);
                v_currNamespace_6754_ = crate::leanh::lean_ctor_get(v___y_6714_, 6);
                v_openDecls_6755_ = crate::leanh::lean_ctor_get(v___y_6714_, 7);
                v_initHeartbeats_6756_ = crate::leanh::lean_ctor_get(v___y_6714_, 8);
                v_maxHeartbeats_6757_ = crate::leanh::lean_ctor_get(v___y_6714_, 9);
                v_quotContext_6758_ = crate::leanh::lean_ctor_get(v___y_6714_, 10);
                v_currMacroScope_6759_ = crate::leanh::lean_ctor_get(v___y_6714_, 11);
                v_diag_6760_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6714_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6761_ = crate::leanh::lean_ctor_get(v___y_6714_, 12);
                v_suppressElabErrors_6762_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6714_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6763_ = crate::leanh::lean_ctor_get(v___y_6714_, 13);
                if crate::leanh::lean_obj_tag(v_cancelTk_x3f_6761_) == 1 {
                    v_val_6769_ = crate::leanh::lean_ctor_get(v_cancelTk_x3f_6761_, 0);
                    v___x_6770_ = l_IO_CancelToken_isSet(v_val_6769_);
                    if v___x_6770_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_6710_);
                        v___x_6771_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__8___redArg();
                        v_a_6772_ = crate::leanh::lean_ctor_get(v___x_6771_, 0);
                        v_isSharedCheck_6779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6771_)) as u8;
                        if v_isSharedCheck_6779_ == 0 {
                            v___x_6774_ = v___x_6771_;
                            v_isShared_6775_ = v_isSharedCheck_6779_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6772_);
                            crate::leanh::lean_dec(v___x_6771_);
                            v___x_6774_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___y_6718_) == 0 {
                    return v___y_6718_;
                } else {
                    v_a_6719_ = crate::leanh::lean_ctor_get(v___y_6718_, 0);
                    v_isSharedCheck_6726_ = (!crate::leanh::lean_is_exclusive(v___y_6718_)) as u8;
                    if v_isSharedCheck_6726_ == 0 {
                        v___x_6721_ = v___y_6718_;
                        v_isShared_6722_ = v_isSharedCheck_6726_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6719_);
                        crate::leanh::lean_dec(v___y_6718_);
                        v___x_6721_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6725_, 0, v_a_6719_);
                    v___x_6724_ = v_reuseFailAlloc_6725_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6724_;
            }
            4 => {
                v___x_6744_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6745_ = lean_nat_add(v___y_6728_, v___x_6744_);
                crate::leanh::lean_inc_ref(v___y_6737_);
                crate::leanh::lean_inc(v___y_6736_);
                crate::leanh::lean_inc(v___y_6735_);
                crate::leanh::lean_inc(v___y_6743_);
                crate::leanh::lean_inc(v___y_6733_);
                crate::leanh::lean_inc(v___y_6741_);
                crate::leanh::lean_inc(v___y_6732_);
                crate::leanh::lean_inc(v___y_6730_);
                crate::leanh::lean_inc(v___y_6729_);
                crate::leanh::lean_inc_ref(v___y_6740_);
                crate::leanh::lean_inc_ref(v___y_6742_);
                crate::leanh::lean_inc_ref(v___y_6734_);
                v___x_6746_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_6746_, 0, v___y_6734_);
                crate::leanh::lean_ctor_set(v___x_6746_, 1, v___y_6742_);
                crate::leanh::lean_ctor_set(v___x_6746_, 2, v___y_6740_);
                crate::leanh::lean_ctor_set(v___x_6746_, 3, v___x_6745_);
                crate::leanh::lean_ctor_set(v___x_6746_, 4, v___y_6729_);
                crate::leanh::lean_ctor_set(v___x_6746_, 5, v___y_6731_);
                crate::leanh::lean_ctor_set(v___x_6746_, 6, v___y_6730_);
                crate::leanh::lean_ctor_set(v___x_6746_, 7, v___y_6732_);
                crate::leanh::lean_ctor_set(v___x_6746_, 8, v___y_6741_);
                crate::leanh::lean_ctor_set(v___x_6746_, 9, v___y_6733_);
                crate::leanh::lean_ctor_set(v___x_6746_, 10, v___y_6743_);
                crate::leanh::lean_ctor_set(v___x_6746_, 11, v___y_6735_);
                crate::leanh::lean_ctor_set(v___x_6746_, 12, v___y_6736_);
                crate::leanh::lean_ctor_set(v___x_6746_, 13, v___y_6737_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_6738_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v___y_6739_,
                );
                crate::leanh::lean_inc(v___y_6715_);
                crate::leanh::lean_inc(v___y_6713_);
                crate::leanh::lean_inc_ref(v___y_6712_);
                crate::leanh::lean_inc(v___y_6711_);
                v___x_6747_ = crate::leanh::lean_apply_6(
                    v_x_6710_,
                    v___y_6711_,
                    v___y_6712_,
                    v___y_6713_,
                    v___x_6746_,
                    v___y_6715_,
                    crate::leanh::lean_box(0),
                );
                v___y_6718_ = v___x_6747_;
                state = 1;
                continue;
            }
            5 => {
                v___x_6765_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6766_ = lean_nat_dec_eq(v_maxRecDepth_6752_, v___x_6765_);
                if v___x_6766_ == 0 {
                    v___x_6767_ = lean_nat_dec_eq(v_currRecDepth_6751_, v_maxRecDepth_6752_);
                    if v___x_6767_ == 0 {
                        crate::leanh::lean_inc(v_ref_6753_);
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
                        crate::leanh::lean_dec_ref(v_x_6710_);
                        crate::leanh::lean_inc(v_ref_6753_);
                        v___x_6768_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_6753_);
                        v___y_6718_ = v___x_6768_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_ref_6753_);
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
                    v_reuseFailAlloc_6778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6772_);
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
    mut v_x_6780_: *mut crate::leanh::LeanObject,
    mut v___y_6781_: *mut crate::leanh::LeanObject,
    mut v___y_6782_: *mut crate::leanh::LeanObject,
    mut v___y_6783_: *mut crate::leanh::LeanObject,
    mut v___y_6784_: *mut crate::leanh::LeanObject,
    mut v___y_6785_: *mut crate::leanh::LeanObject,
    mut v___y_6786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6787_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_6780_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_, v___y_6785_);
    crate::leanh::lean_dec(v___y_6785_);
    crate::leanh::lean_dec_ref(v___y_6784_);
    crate::leanh::lean_dec(v___y_6783_);
    crate::leanh::lean_dec_ref(v___y_6782_);
    crate::leanh::lean_dec(v___y_6781_);
    return v_res_6787_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(
    mut v_00_u03b1_6788_: *mut crate::leanh::LeanObject,
    mut v_x_6789_: *mut crate::leanh::LeanObject,
    mut v___y_6790_: *mut crate::leanh::LeanObject,
    mut v___y_6791_: *mut crate::leanh::LeanObject,
    mut v___y_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6795_ = crate::leanh::lean_apply_1(v_x_6789_, crate::leanh::lean_box(0));
    v___x_6796_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6796_, 0, v___x_6795_);
    return v___x_6796_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_6797_: *mut crate::leanh::LeanObject,
    mut v_x_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
    mut v___y_6800_: *mut crate::leanh::LeanObject,
    mut v___y_6801_: *mut crate::leanh::LeanObject,
    mut v___y_6802_: *mut crate::leanh::LeanObject,
    mut v___y_6803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6804_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(v_00_u03b1_6797_, v_x_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_);
    crate::leanh::lean_dec(v___y_6802_);
    crate::leanh::lean_dec_ref(v___y_6801_);
    crate::leanh::lean_dec(v___y_6800_);
    crate::leanh::lean_dec_ref(v___y_6799_);
    return v_res_6804_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(
    mut v_pre_6805_: *mut crate::leanh::LeanObject,
    mut v_post_6806_: *mut crate::leanh::LeanObject,
    mut v_sz_6807_: usize,
    mut v_i_6808_: usize,
    mut v_bs_6809_: *mut crate::leanh::LeanObject,
    mut v___y_6810_: *mut crate::leanh::LeanObject,
    mut v___y_6811_: *mut crate::leanh::LeanObject,
    mut v___y_6812_: *mut crate::leanh::LeanObject,
    mut v___y_6813_: *mut crate::leanh::LeanObject,
    mut v___y_6814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6816_: u8 = 0;
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: usize = 0;
    let mut v___x_6824_: usize = 0;
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6830_: u8 = 0;
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6816_ = lean_usize_dec_lt(v_i_6808_, v_sz_6807_);
                if v___x_6816_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_6806_);
                    crate::leanh::lean_dec_ref(v_pre_6805_);
                    v___x_6817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6817_, 0, v_bs_6809_);
                    return v___x_6817_;
                } else {
                    v_v_6818_ = lean_array_uget_borrowed(v_bs_6809_, v_i_6808_);
                    crate::leanh::lean_inc(v_v_6818_);
                    crate::leanh::lean_inc_ref(v_post_6806_);
                    crate::leanh::lean_inc_ref(v_pre_6805_);
                    v___x_6819_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6805_, v_post_6806_, v_v_6818_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_, v___y_6814_);
                    if crate::leanh::lean_obj_tag(v___x_6819_) == 0 {
                        v_a_6820_ = crate::leanh::lean_ctor_get(v___x_6819_, 0);
                        crate::leanh::lean_inc(v_a_6820_);
                        crate::leanh::lean_dec_ref_known(v___x_6819_, 1);
                        v___x_6821_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_6822_ = lean_array_uset(v_bs_6809_, v_i_6808_, v___x_6821_);
                        v___x_6823_ = 1usize;
                        v___x_6824_ = lean_usize_add(v_i_6808_, v___x_6823_);
                        v___x_6825_ = lean_array_uset(v_bs_x27_6822_, v_i_6808_, v_a_6820_);
                        v_i_6808_ = v___x_6824_;
                        v_bs_6809_ = v___x_6825_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_6809_);
                        crate::leanh::lean_dec_ref(v_post_6806_);
                        crate::leanh::lean_dec_ref(v_pre_6805_);
                        v_a_6827_ = crate::leanh::lean_ctor_get(v___x_6819_, 0);
                        v_isSharedCheck_6834_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6819_)) as u8;
                        if v_isSharedCheck_6834_ == 0 {
                            v___x_6829_ = v___x_6819_;
                            v_isShared_6830_ = v_isSharedCheck_6834_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6827_);
                            crate::leanh::lean_dec(v___x_6819_);
                            v___x_6829_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6827_);
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
    mut v_pre_6835_: *mut crate::leanh::LeanObject,
    mut v_post_6836_: *mut crate::leanh::LeanObject,
    mut v_x_6837_: *mut crate::leanh::LeanObject,
    mut v_x_6838_: *mut crate::leanh::LeanObject,
    mut v_x_6839_: *mut crate::leanh::LeanObject,
    mut v___y_6840_: *mut crate::leanh::LeanObject,
    mut v___y_6841_: *mut crate::leanh::LeanObject,
    mut v___y_6842_: *mut crate::leanh::LeanObject,
    mut v___y_6843_: *mut crate::leanh::LeanObject,
    mut v___y_6844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6854_: usize = 0;
    let mut v___x_6855_: usize = 0;
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6863_: u8 = 0;
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6837_) == 5 {
                    v_fn_6846_ = crate::leanh::lean_ctor_get(v_x_6837_, 0);
                    crate::leanh::lean_inc_ref(v_fn_6846_);
                    v_arg_6847_ = crate::leanh::lean_ctor_get(v_x_6837_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6847_);
                    crate::leanh::lean_dec_ref_known(v_x_6837_, 2);
                    v___x_6848_ = lean_array_set(v_x_6838_, v_x_6839_, v_arg_6847_);
                    v___x_6849_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6850_ = lean_nat_sub(v_x_6839_, v___x_6849_);
                    crate::leanh::lean_dec(v_x_6839_);
                    v_x_6837_ = v_fn_6846_;
                    v_x_6838_ = v___x_6848_;
                    v_x_6839_ = v___x_6850_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_6839_);
                    crate::leanh::lean_inc_ref(v_post_6836_);
                    crate::leanh::lean_inc_ref(v_pre_6835_);
                    v___x_6852_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6835_, v_post_6836_, v_x_6837_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
                    if crate::leanh::lean_obj_tag(v___x_6852_) == 0 {
                        v_a_6853_ = crate::leanh::lean_ctor_get(v___x_6852_, 0);
                        crate::leanh::lean_inc(v_a_6853_);
                        crate::leanh::lean_dec_ref_known(v___x_6852_, 1);
                        v_sz_6854_ = lean_array_size(v_x_6838_);
                        v___x_6855_ = 0usize;
                        crate::leanh::lean_inc_ref(v_post_6836_);
                        crate::leanh::lean_inc_ref(v_pre_6835_);
                        v___x_6856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_6835_, v_post_6836_, v_sz_6854_, v___x_6855_, v_x_6838_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
                        if crate::leanh::lean_obj_tag(v___x_6856_) == 0 {
                            v_a_6857_ = crate::leanh::lean_ctor_get(v___x_6856_, 0);
                            crate::leanh::lean_inc(v_a_6857_);
                            crate::leanh::lean_dec_ref_known(v___x_6856_, 1);
                            v___x_6858_ = l_Lean_mkAppN(v_a_6853_, v_a_6857_);
                            crate::leanh::lean_dec(v_a_6857_);
                            v___x_6859_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6835_, v_post_6836_, v___x_6858_, v___y_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_);
                            return v___x_6859_;
                        } else {
                            crate::leanh::lean_dec(v_a_6853_);
                            crate::leanh::lean_dec_ref(v_post_6836_);
                            crate::leanh::lean_dec_ref(v_pre_6835_);
                            v_a_6860_ = crate::leanh::lean_ctor_get(v___x_6856_, 0);
                            v_isSharedCheck_6867_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6856_)) as u8;
                            if v_isSharedCheck_6867_ == 0 {
                                v___x_6862_ = v___x_6856_;
                                v_isShared_6863_ = v_isSharedCheck_6867_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6860_);
                                crate::leanh::lean_dec(v___x_6856_);
                                v___x_6862_ = crate::leanh::lean_box(0);
                                v_isShared_6863_ = v_isSharedCheck_6867_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_6838_);
                        crate::leanh::lean_dec_ref(v_post_6836_);
                        crate::leanh::lean_dec_ref(v_pre_6835_);
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
                    v_reuseFailAlloc_6866_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6866_, 0, v_a_6860_);
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
    mut v___x_6868_: *mut crate::leanh::LeanObject,
    mut v_pre_6869_: *mut crate::leanh::LeanObject,
    mut v_e_6870_: *mut crate::leanh::LeanObject,
    mut v_post_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
    mut v___y_6874_: *mut crate::leanh::LeanObject,
    mut v___y_6875_: *mut crate::leanh::LeanObject,
    mut v___y_6876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6885_: u8 = 0;
    let mut v___y_6886_: u8 = 0;
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: usize = 0;
    let mut v___x_6890_: usize = 0;
    let mut v___x_6891_: u8 = 0;
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: u8 = 0;
    let mut v___y_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6901_: u8 = 0;
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: u8 = 0;
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6912_: u8 = 0;
    let mut v___y_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6914_: u8 = 0;
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: u8 = 0;
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6926_: u8 = 0;
    let mut v___y_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6932_: u8 = 0;
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: usize = 0;
    let mut v___x_6938_: usize = 0;
    let mut v___x_6939_: u8 = 0;
    let mut v___x_6940_: usize = 0;
    let mut v___x_6941_: usize = 0;
    let mut v___x_6942_: u8 = 0;
    let mut v_binderName_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6946_: u8 = 0;
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: usize = 0;
    let mut v___x_6952_: usize = 0;
    let mut v___x_6953_: u8 = 0;
    let mut v___x_6954_: usize = 0;
    let mut v___x_6955_: usize = 0;
    let mut v___x_6956_: u8 = 0;
    let mut v_declName_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6961_: u8 = 0;
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: usize = 0;
    let mut v___x_6969_: usize = 0;
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: usize = 0;
    let mut v___x_6972_: usize = 0;
    let mut v___x_6973_: u8 = 0;
    let mut v_dummy_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: usize = 0;
    let mut v___x_6985_: usize = 0;
    let mut v___x_6986_: u8 = 0;
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: usize = 0;
    let mut v___x_6996_: usize = 0;
    let mut v___x_6997_: u8 = 0;
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7012_: u8 = 0;
    let mut v_a_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7016_: u8 = 0;
    let mut v___x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7020_: u8 = 0;
    let mut v_a_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7024_: u8 = 0;
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6921_ = l_Lean_Core_checkSystem(v___x_6868_, v___y_6875_, v___y_6876_);
                if crate::leanh::lean_obj_tag(v___x_6921_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6921_, 1);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    crate::leanh::lean_inc(v___y_6876_);
                    crate::leanh::lean_inc_ref(v___y_6875_);
                    crate::leanh::lean_inc(v___y_6874_);
                    crate::leanh::lean_inc_ref(v___y_6873_);
                    crate::leanh::lean_inc_ref(v_e_6870_);
                    v___x_6922_ = crate::leanh::lean_apply_6(
                        v_pre_6869_,
                        v_e_6870_,
                        v___y_6873_,
                        v___y_6874_,
                        v___y_6875_,
                        v___y_6876_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6922_) == 0 {
                        v_a_6923_ = crate::leanh::lean_ctor_get(v___x_6922_, 0);
                        v_isSharedCheck_7012_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6922_)) as u8;
                        if v_isSharedCheck_7012_ == 0 {
                            v___x_6925_ = v___x_6922_;
                            v_isShared_6926_ = v_isSharedCheck_7012_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6923_);
                            crate::leanh::lean_dec(v___x_6922_);
                            v___x_6925_ = crate::leanh::lean_box(0);
                            v_isShared_6926_ = v_isSharedCheck_7012_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_e_6870_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
                        v_a_7013_ = crate::leanh::lean_ctor_get(v___x_6922_, 0);
                        v_isSharedCheck_7020_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6922_)) as u8;
                        if v_isSharedCheck_7020_ == 0 {
                            v___x_7015_ = v___x_6922_;
                            v_isShared_7016_ = v_isSharedCheck_7020_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7013_);
                            crate::leanh::lean_dec(v___x_6922_);
                            v___x_7015_ = crate::leanh::lean_box(0);
                            v_isShared_7016_ = v_isSharedCheck_7020_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_6871_);
                    crate::leanh::lean_dec_ref(v_e_6870_);
                    crate::leanh::lean_dec_ref(v_pre_6869_);
                    v_a_7021_ = crate::leanh::lean_ctor_get(v___x_6921_, 0);
                    v_isSharedCheck_7028_ = (!crate::leanh::lean_is_exclusive(v___x_6921_)) as u8;
                    if v_isSharedCheck_7028_ == 0 {
                        v___x_7023_ = v___x_6921_;
                        v_isShared_7024_ = v_isSharedCheck_7028_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7021_);
                        crate::leanh::lean_dec(v___x_6921_);
                        v___x_7023_ = crate::leanh::lean_box(0);
                        v_isShared_7024_ = v_isSharedCheck_7028_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6886_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6884_);
                    crate::leanh::lean_dec_ref(v___y_6879_);
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
                    crate::leanh::lean_dec_ref(v___y_6879_);
                    v___x_6890_ = lean_ptr_addr(v___y_6883_);
                    v___x_6891_ = lean_usize_dec_eq(v___x_6889_, v___x_6890_);
                    if v___x_6891_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_6884_);
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
                        crate::leanh::lean_dec_ref(v___y_6883_);
                        crate::leanh::lean_dec(v___y_6882_);
                        crate::leanh::lean_dec_ref(v___y_6881_);
                        crate::leanh::lean_dec_ref(v___y_6880_);
                        v___x_6894_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6884_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6894_;
                    }
                }
            }
            2 => {
                if v___y_6901_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6900_);
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
                        crate::leanh::lean_dec_ref(v___y_6900_);
                        v___x_6905_ = l_Lean_Expr_lam___override(
                            v___y_6898_,
                            v___y_6897_,
                            v___y_6896_,
                            v___y_6899_,
                        );
                        v___x_6906_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6905_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6906_;
                    } else {
                        crate::leanh::lean_dec(v___y_6898_);
                        crate::leanh::lean_dec_ref(v___y_6897_);
                        crate::leanh::lean_dec_ref(v___y_6896_);
                        v___x_6907_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6900_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6907_;
                    }
                }
            }
            3 => {
                if v___y_6914_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6911_);
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
                        crate::leanh::lean_dec_ref(v___y_6911_);
                        v___x_6918_ = l_Lean_Expr_forallE___override(
                            v___y_6913_,
                            v___y_6910_,
                            v___y_6909_,
                            v___y_6912_,
                        );
                        v___x_6919_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6918_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6919_;
                    } else {
                        crate::leanh::lean_dec(v___y_6913_);
                        crate::leanh::lean_dec_ref(v___y_6910_);
                        crate::leanh::lean_dec_ref(v___y_6909_);
                        v___x_6920_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6911_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_6920_;
                    }
                }
            }
            4 => match crate::leanh::lean_obj_tag(v_a_6923_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_6871_);
                    crate::leanh::lean_dec_ref(v_e_6870_);
                    crate::leanh::lean_dec_ref(v_pre_6869_);
                    v_e_7002_ = crate::leanh::lean_ctor_get(v_a_6923_, 0);
                    crate::leanh::lean_inc_ref(v_e_7002_);
                    crate::leanh::lean_dec_ref_known(v_a_6923_, 1);
                    if v_isShared_6926_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6925_, 0, v_e_7002_);
                        v___x_7004_ = v___x_6925_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7005_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7005_, 0, v_e_7002_);
                        v___x_7004_ = v_reuseFailAlloc_7005_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6925_);
                    crate::leanh::lean_dec_ref(v_e_6870_);
                    v_e_7006_ = crate::leanh::lean_ctor_get(v_a_6923_, 0);
                    crate::leanh::lean_inc_ref(v_e_7006_);
                    crate::leanh::lean_dec_ref_known(v_a_6923_, 1);
                    crate::leanh::lean_inc_ref(v_post_6871_);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    v___x_7007_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_e_7006_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if crate::leanh::lean_obj_tag(v___x_7007_) == 0 {
                        v_a_7008_ = crate::leanh::lean_ctor_get(v___x_7007_, 0);
                        crate::leanh::lean_inc(v_a_7008_);
                        crate::leanh::lean_dec_ref_known(v___x_7007_, 1);
                        v___x_7009_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v_a_7008_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        return v___x_7009_;
                    } else {
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_7007_;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_6925_);
                    v_e_x3f_7010_ = crate::leanh::lean_ctor_get(v_a_6923_, 0);
                    crate::leanh::lean_inc(v_e_x3f_7010_);
                    crate::leanh::lean_dec_ref_known(v_a_6923_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_7010_) == 0 {
                        v___y_6928_ = v_e_6870_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6870_);
                        v_val_7011_ = crate::leanh::lean_ctor_get(v_e_x3f_7010_, 0);
                        crate::leanh::lean_inc(v_val_7011_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_7010_, 1);
                        v___y_6928_ = v_val_7011_;
                        state = 5;
                        continue;
                    }
                }
            },
            5 => match crate::leanh::lean_obj_tag(v___y_6928_) {
                7 => {
                    v_binderName_6929_ = crate::leanh::lean_ctor_get(v___y_6928_, 0);
                    crate::leanh::lean_inc(v_binderName_6929_);
                    v_binderType_6930_ = crate::leanh::lean_ctor_get(v___y_6928_, 1);
                    v_body_6931_ = crate::leanh::lean_ctor_get(v___y_6928_, 2);
                    v_binderInfo_6932_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6928_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_6930_);
                    crate::leanh::lean_inc_ref(v_post_6871_);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_binderType_6930_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if crate::leanh::lean_obj_tag(v___x_6933_) == 0 {
                        v_a_6934_ = crate::leanh::lean_ctor_get(v___x_6933_, 0);
                        crate::leanh::lean_inc(v_a_6934_);
                        crate::leanh::lean_dec_ref_known(v___x_6933_, 1);
                        crate::leanh::lean_inc_ref(v_body_6931_);
                        crate::leanh::lean_inc_ref(v_post_6871_);
                        crate::leanh::lean_inc_ref(v_pre_6869_);
                        v___x_6935_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_body_6931_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        if crate::leanh::lean_obj_tag(v___x_6935_) == 0 {
                            v_a_6936_ = crate::leanh::lean_ctor_get(v___x_6935_, 0);
                            crate::leanh::lean_inc(v_a_6936_);
                            crate::leanh::lean_dec_ref_known(v___x_6935_, 1);
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
                            crate::leanh::lean_dec(v_a_6934_);
                            crate::leanh::lean_dec_ref_known(v___y_6928_, 3);
                            crate::leanh::lean_dec(v_binderName_6929_);
                            crate::leanh::lean_dec_ref(v_post_6871_);
                            crate::leanh::lean_dec_ref(v_pre_6869_);
                            return v___x_6935_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6928_, 3);
                        crate::leanh::lean_dec(v_binderName_6929_);
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6933_;
                    }
                }
                6 => {
                    v_binderName_6943_ = crate::leanh::lean_ctor_get(v___y_6928_, 0);
                    crate::leanh::lean_inc(v_binderName_6943_);
                    v_binderType_6944_ = crate::leanh::lean_ctor_get(v___y_6928_, 1);
                    v_body_6945_ = crate::leanh::lean_ctor_get(v___y_6928_, 2);
                    v_binderInfo_6946_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6928_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_6944_);
                    crate::leanh::lean_inc_ref(v_post_6871_);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6947_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_binderType_6944_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if crate::leanh::lean_obj_tag(v___x_6947_) == 0 {
                        v_a_6948_ = crate::leanh::lean_ctor_get(v___x_6947_, 0);
                        crate::leanh::lean_inc(v_a_6948_);
                        crate::leanh::lean_dec_ref_known(v___x_6947_, 1);
                        crate::leanh::lean_inc_ref(v_body_6945_);
                        crate::leanh::lean_inc_ref(v_post_6871_);
                        crate::leanh::lean_inc_ref(v_pre_6869_);
                        v___x_6949_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_body_6945_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        if crate::leanh::lean_obj_tag(v___x_6949_) == 0 {
                            v_a_6950_ = crate::leanh::lean_ctor_get(v___x_6949_, 0);
                            crate::leanh::lean_inc(v_a_6950_);
                            crate::leanh::lean_dec_ref_known(v___x_6949_, 1);
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
                            crate::leanh::lean_dec(v_a_6948_);
                            crate::leanh::lean_dec_ref_known(v___y_6928_, 3);
                            crate::leanh::lean_dec(v_binderName_6943_);
                            crate::leanh::lean_dec_ref(v_post_6871_);
                            crate::leanh::lean_dec_ref(v_pre_6869_);
                            return v___x_6949_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6928_, 3);
                        crate::leanh::lean_dec(v_binderName_6943_);
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6947_;
                    }
                }
                8 => {
                    v_declName_6957_ = crate::leanh::lean_ctor_get(v___y_6928_, 0);
                    crate::leanh::lean_inc(v_declName_6957_);
                    v_type_6958_ = crate::leanh::lean_ctor_get(v___y_6928_, 1);
                    v_value_6959_ = crate::leanh::lean_ctor_get(v___y_6928_, 2);
                    v_body_6960_ = crate::leanh::lean_ctor_get(v___y_6928_, 3);
                    crate::leanh::lean_inc_ref(v_body_6960_);
                    v_nondep_6961_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6928_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_type_6958_);
                    crate::leanh::lean_inc_ref(v_post_6871_);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6962_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_type_6958_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if crate::leanh::lean_obj_tag(v___x_6962_) == 0 {
                        v_a_6963_ = crate::leanh::lean_ctor_get(v___x_6962_, 0);
                        crate::leanh::lean_inc(v_a_6963_);
                        crate::leanh::lean_dec_ref_known(v___x_6962_, 1);
                        crate::leanh::lean_inc_ref(v_value_6959_);
                        crate::leanh::lean_inc_ref(v_post_6871_);
                        crate::leanh::lean_inc_ref(v_pre_6869_);
                        v___x_6964_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_value_6959_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                        if crate::leanh::lean_obj_tag(v___x_6964_) == 0 {
                            v_a_6965_ = crate::leanh::lean_ctor_get(v___x_6964_, 0);
                            crate::leanh::lean_inc(v_a_6965_);
                            crate::leanh::lean_dec_ref_known(v___x_6964_, 1);
                            crate::leanh::lean_inc_ref(v_body_6960_);
                            crate::leanh::lean_inc_ref(v_post_6871_);
                            crate::leanh::lean_inc_ref(v_pre_6869_);
                            v___x_6966_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_body_6960_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            if crate::leanh::lean_obj_tag(v___x_6966_) == 0 {
                                v_a_6967_ = crate::leanh::lean_ctor_get(v___x_6966_, 0);
                                crate::leanh::lean_inc(v_a_6967_);
                                crate::leanh::lean_dec_ref_known(v___x_6966_, 1);
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
                                crate::leanh::lean_dec(v_a_6965_);
                                crate::leanh::lean_dec(v_a_6963_);
                                crate::leanh::lean_dec_ref(v_body_6960_);
                                crate::leanh::lean_dec_ref_known(v___y_6928_, 4);
                                crate::leanh::lean_dec(v_declName_6957_);
                                crate::leanh::lean_dec_ref(v_post_6871_);
                                crate::leanh::lean_dec_ref(v_pre_6869_);
                                return v___x_6966_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6963_);
                            crate::leanh::lean_dec_ref(v_body_6960_);
                            crate::leanh::lean_dec_ref_known(v___y_6928_, 4);
                            crate::leanh::lean_dec(v_declName_6957_);
                            crate::leanh::lean_dec_ref(v_post_6871_);
                            crate::leanh::lean_dec_ref(v_pre_6869_);
                            return v___x_6964_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_6960_);
                        crate::leanh::lean_dec(v_declName_6957_);
                        crate::leanh::lean_dec_ref_known(v___y_6928_, 4);
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6962_;
                    }
                }
                5 => {
                    v_dummy_6974_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once), _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
                    v_nargs_6975_ = l_Lean_Expr_getAppNumArgs(v___y_6928_);
                    crate::leanh::lean_inc(v_nargs_6975_);
                    v___x_6976_ = lean_mk_array(v_nargs_6975_, v_dummy_6974_);
                    v___x_6977_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6978_ = lean_nat_sub(v_nargs_6975_, v___x_6977_);
                    crate::leanh::lean_dec(v_nargs_6975_);
                    v___x_6979_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_6869_, v_post_6871_, v___y_6928_, v___x_6976_, v___x_6978_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    return v___x_6979_;
                }
                10 => {
                    v_data_6980_ = crate::leanh::lean_ctor_get(v___y_6928_, 0);
                    v_expr_6981_ = crate::leanh::lean_ctor_get(v___y_6928_, 1);
                    crate::leanh::lean_inc_ref(v_expr_6981_);
                    crate::leanh::lean_inc_ref(v_post_6871_);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6982_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_expr_6981_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if crate::leanh::lean_obj_tag(v___x_6982_) == 0 {
                        v_a_6983_ = crate::leanh::lean_ctor_get(v___x_6982_, 0);
                        crate::leanh::lean_inc(v_a_6983_);
                        crate::leanh::lean_dec_ref_known(v___x_6982_, 1);
                        v___x_6984_ = lean_ptr_addr(v_expr_6981_);
                        v___x_6985_ = lean_ptr_addr(v_a_6983_);
                        v___x_6986_ = lean_usize_dec_eq(v___x_6984_, v___x_6985_);
                        if v___x_6986_ == 0 {
                            crate::leanh::lean_inc(v_data_6980_);
                            crate::leanh::lean_dec_ref_known(v___y_6928_, 2);
                            v___x_6987_ = l_Lean_Expr_mdata___override(v_data_6980_, v_a_6983_);
                            v___x_6988_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6987_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_6988_;
                        } else {
                            crate::leanh::lean_dec(v_a_6983_);
                            v___x_6989_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6928_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_6989_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6928_, 2);
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
                        return v___x_6982_;
                    }
                }
                11 => {
                    v_typeName_6990_ = crate::leanh::lean_ctor_get(v___y_6928_, 0);
                    v_idx_6991_ = crate::leanh::lean_ctor_get(v___y_6928_, 1);
                    v_struct_6992_ = crate::leanh::lean_ctor_get(v___y_6928_, 2);
                    crate::leanh::lean_inc_ref(v_struct_6992_);
                    crate::leanh::lean_inc_ref(v_post_6871_);
                    crate::leanh::lean_inc_ref(v_pre_6869_);
                    v___x_6993_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_6869_, v_post_6871_, v_struct_6992_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                    if crate::leanh::lean_obj_tag(v___x_6993_) == 0 {
                        v_a_6994_ = crate::leanh::lean_ctor_get(v___x_6993_, 0);
                        crate::leanh::lean_inc(v_a_6994_);
                        crate::leanh::lean_dec_ref_known(v___x_6993_, 1);
                        v___x_6995_ = lean_ptr_addr(v_struct_6992_);
                        v___x_6996_ = lean_ptr_addr(v_a_6994_);
                        v___x_6997_ = lean_usize_dec_eq(v___x_6995_, v___x_6996_);
                        if v___x_6997_ == 0 {
                            crate::leanh::lean_inc(v_idx_6991_);
                            crate::leanh::lean_inc(v_typeName_6990_);
                            crate::leanh::lean_dec_ref_known(v___y_6928_, 3);
                            v___x_6998_ = l_Lean_Expr_proj___override(
                                v_typeName_6990_,
                                v_idx_6991_,
                                v_a_6994_,
                            );
                            v___x_6999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___x_6998_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_6999_;
                        } else {
                            crate::leanh::lean_dec(v_a_6994_);
                            v___x_7000_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_6869_, v_post_6871_, v___y_6928_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                            return v___x_7000_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_6928_, 3);
                        crate::leanh::lean_dec_ref(v_post_6871_);
                        crate::leanh::lean_dec_ref(v_pre_6869_);
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
                    v_reuseFailAlloc_7019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7019_, 0, v_a_7013_);
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
                    v_reuseFailAlloc_7027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 0, v_a_7021_);
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
    mut v___x_7029_: *mut crate::leanh::LeanObject,
    mut v_pre_7030_: *mut crate::leanh::LeanObject,
    mut v_e_7031_: *mut crate::leanh::LeanObject,
    mut v_post_7032_: *mut crate::leanh::LeanObject,
    mut v___y_7033_: *mut crate::leanh::LeanObject,
    mut v___y_7034_: *mut crate::leanh::LeanObject,
    mut v___y_7035_: *mut crate::leanh::LeanObject,
    mut v___y_7036_: *mut crate::leanh::LeanObject,
    mut v___y_7037_: *mut crate::leanh::LeanObject,
    mut v___y_7038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7039_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_7029_, v_pre_7030_, v_e_7031_, v_post_7032_, v___y_7033_, v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_);
    crate::leanh::lean_dec(v___y_7037_);
    crate::leanh::lean_dec_ref(v___y_7036_);
    crate::leanh::lean_dec(v___y_7035_);
    crate::leanh::lean_dec_ref(v___y_7034_);
    crate::leanh::lean_dec(v___y_7033_);
    return v_res_7039_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(
    mut v_pre_7040_: *mut crate::leanh::LeanObject,
    mut v_post_7041_: *mut crate::leanh::LeanObject,
    mut v_e_7042_: *mut crate::leanh::LeanObject,
    mut v_a_7043_: *mut crate::leanh::LeanObject,
    mut v___y_7044_: *mut crate::leanh::LeanObject,
    mut v___y_7045_: *mut crate::leanh::LeanObject,
    mut v___y_7046_: *mut crate::leanh::LeanObject,
    mut v___y_7047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7054_: u8 = 0;
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7064_: u8 = 0;
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7068_: u8 = 0;
    let mut v_unused_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7073_: u8 = 0;
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7077_: u8 = 0;
    let mut v_val_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7082_: u8 = 0;
    let mut v_a_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7086_: u8 = 0;
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_7043_);
                v___x_7049_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_7049_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_7049_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_7049_, 2, v_a_7043_);
                v___x_7050_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_7049_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                if crate::leanh::lean_obj_tag(v___x_7050_) == 0 {
                    v_a_7051_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7082_ = (!crate::leanh::lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7082_ == 0 {
                        v___x_7053_ = v___x_7050_;
                        v_isShared_7054_ = v_isSharedCheck_7082_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7051_);
                        crate::leanh::lean_dec(v___x_7050_);
                        v___x_7053_ = crate::leanh::lean_box(0);
                        v_isShared_7054_ = v_isSharedCheck_7082_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7042_);
                    crate::leanh::lean_dec_ref(v_post_7041_);
                    crate::leanh::lean_dec_ref(v_pre_7040_);
                    v_a_7083_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7090_ = (!crate::leanh::lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7090_ == 0 {
                        v___x_7085_ = v___x_7050_;
                        v_isShared_7086_ = v_isSharedCheck_7090_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7083_);
                        crate::leanh::lean_dec(v___x_7050_);
                        v___x_7085_ = crate::leanh::lean_box(0);
                        v_isShared_7086_ = v_isSharedCheck_7090_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_7051_, v_e_7042_);
                crate::leanh::lean_dec(v_a_7051_);
                if crate::leanh::lean_obj_tag(v___x_7055_) == 0 {
                    crate::leanh::lean_del_object(v___x_7053_);
                    v___x_7056_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0;
                    crate::leanh::lean_inc_ref(v_e_7042_);
                    v___f_7057_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 10, 4);
                    crate::leanh::lean_closure_set(v___f_7057_, 0, v___x_7056_);
                    crate::leanh::lean_closure_set(v___f_7057_, 1, v_pre_7040_);
                    crate::leanh::lean_closure_set(v___f_7057_, 2, v_e_7042_);
                    crate::leanh::lean_closure_set(v___f_7057_, 3, v_post_7041_);
                    v___x_7058_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_7057_, v_a_7043_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                    if crate::leanh::lean_obj_tag(v___x_7058_) == 0 {
                        v_a_7059_ = crate::leanh::lean_ctor_get(v___x_7058_, 0);
                        crate::leanh::lean_inc_n(v_a_7059_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_7058_, 1);
                        crate::leanh::lean_inc(v_a_7043_);
                        v___f_7060_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_7060_, 0, v_a_7043_);
                        crate::leanh::lean_closure_set(v___f_7060_, 1, v_e_7042_);
                        crate::leanh::lean_closure_set(v___f_7060_, 2, v_a_7059_);
                        v___x_7061_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_7060_, v___y_7044_, v___y_7045_, v___y_7046_, v___y_7047_);
                        if crate::leanh::lean_obj_tag(v___x_7061_) == 0 {
                            v_isSharedCheck_7068_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7061_)) as u8;
                            if v_isSharedCheck_7068_ == 0 {
                                v_unused_7069_ = crate::leanh::lean_ctor_get(v___x_7061_, 0);
                                crate::leanh::lean_dec(v_unused_7069_);
                                v___x_7063_ = v___x_7061_;
                                v_isShared_7064_ = v_isSharedCheck_7068_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7061_);
                                v___x_7063_ = crate::leanh::lean_box(0);
                                v_isShared_7064_ = v_isSharedCheck_7068_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7059_);
                            v_a_7070_ = crate::leanh::lean_ctor_get(v___x_7061_, 0);
                            v_isSharedCheck_7077_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7061_)) as u8;
                            if v_isSharedCheck_7077_ == 0 {
                                v___x_7072_ = v___x_7061_;
                                v_isShared_7073_ = v_isSharedCheck_7077_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7070_);
                                crate::leanh::lean_dec(v___x_7061_);
                                v___x_7072_ = crate::leanh::lean_box(0);
                                v_isShared_7073_ = v_isSharedCheck_7077_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7042_);
                        return v___x_7058_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7042_);
                    crate::leanh::lean_dec_ref(v_post_7041_);
                    crate::leanh::lean_dec_ref(v_pre_7040_);
                    v_val_7078_ = crate::leanh::lean_ctor_get(v___x_7055_, 0);
                    crate::leanh::lean_inc(v_val_7078_);
                    crate::leanh::lean_dec_ref_known(v___x_7055_, 1);
                    if v_isShared_7054_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7053_, 0, v_val_7078_);
                        v___x_7080_ = v___x_7053_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_val_7078_);
                        v___x_7080_ = v_reuseFailAlloc_7081_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7064_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7063_, 0, v_a_7059_);
                    v___x_7066_ = v___x_7063_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7067_, 0, v_a_7059_);
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
                    v_reuseFailAlloc_7076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7076_, 0, v_a_7070_);
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
                    v_reuseFailAlloc_7089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 0, v_a_7083_);
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
    mut v_pre_7091_: *mut crate::leanh::LeanObject,
    mut v_post_7092_: *mut crate::leanh::LeanObject,
    mut v_e_7093_: *mut crate::leanh::LeanObject,
    mut v_a_7094_: *mut crate::leanh::LeanObject,
    mut v___y_7095_: *mut crate::leanh::LeanObject,
    mut v___y_7096_: *mut crate::leanh::LeanObject,
    mut v___y_7097_: *mut crate::leanh::LeanObject,
    mut v___y_7098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7104_: u8 = 0;
    let mut v_e_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7119_: u8 = 0;
    let mut v_a_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v___x_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_7092_);
                crate::leanh::lean_inc(v___y_7098_);
                crate::leanh::lean_inc_ref(v___y_7097_);
                crate::leanh::lean_inc(v___y_7096_);
                crate::leanh::lean_inc_ref(v___y_7095_);
                crate::leanh::lean_inc_ref(v_e_7093_);
                v___x_7100_ = crate::leanh::lean_apply_6(
                    v_post_7092_,
                    v_e_7093_,
                    v___y_7095_,
                    v___y_7096_,
                    v___y_7097_,
                    v___y_7098_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7100_) == 0 {
                    v_a_7101_ = crate::leanh::lean_ctor_get(v___x_7100_, 0);
                    v_isSharedCheck_7119_ = (!crate::leanh::lean_is_exclusive(v___x_7100_)) as u8;
                    if v_isSharedCheck_7119_ == 0 {
                        v___x_7103_ = v___x_7100_;
                        v_isShared_7104_ = v_isSharedCheck_7119_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7101_);
                        crate::leanh::lean_dec(v___x_7100_);
                        v___x_7103_ = crate::leanh::lean_box(0);
                        v_isShared_7104_ = v_isSharedCheck_7119_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7093_);
                    crate::leanh::lean_dec_ref(v_post_7092_);
                    crate::leanh::lean_dec_ref(v_pre_7091_);
                    v_a_7120_ = crate::leanh::lean_ctor_get(v___x_7100_, 0);
                    v_isSharedCheck_7127_ = (!crate::leanh::lean_is_exclusive(v___x_7100_)) as u8;
                    if v_isSharedCheck_7127_ == 0 {
                        v___x_7122_ = v___x_7100_;
                        v_isShared_7123_ = v_isSharedCheck_7127_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7120_);
                        crate::leanh::lean_dec(v___x_7100_);
                        v___x_7122_ = crate::leanh::lean_box(0);
                        v_isShared_7123_ = v_isSharedCheck_7127_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_7101_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_7093_);
                    crate::leanh::lean_dec_ref(v_post_7092_);
                    crate::leanh::lean_dec_ref(v_pre_7091_);
                    v_e_7105_ = crate::leanh::lean_ctor_get(v_a_7101_, 0);
                    crate::leanh::lean_inc_ref(v_e_7105_);
                    crate::leanh::lean_dec_ref_known(v_a_7101_, 1);
                    if v_isShared_7104_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7103_, 0, v_e_7105_);
                        v___x_7107_ = v___x_7103_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_e_7105_);
                        v___x_7107_ = v_reuseFailAlloc_7108_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_7103_);
                    crate::leanh::lean_dec_ref(v_e_7093_);
                    v_e_7109_ = crate::leanh::lean_ctor_get(v_a_7101_, 0);
                    crate::leanh::lean_inc_ref(v_e_7109_);
                    crate::leanh::lean_dec_ref_known(v_a_7101_, 1);
                    v___x_7110_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_7091_, v_post_7092_, v_e_7109_, v_a_7094_, v___y_7095_, v___y_7096_, v___y_7097_, v___y_7098_);
                    return v___x_7110_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_7092_);
                    crate::leanh::lean_dec_ref(v_pre_7091_);
                    v_e_x3f_7111_ = crate::leanh::lean_ctor_get(v_a_7101_, 0);
                    crate::leanh::lean_inc(v_e_x3f_7111_);
                    crate::leanh::lean_dec_ref_known(v_a_7101_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_7111_) == 0 {
                        if v_isShared_7104_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7103_, 0, v_e_7093_);
                            v___x_7113_ = v___x_7103_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7114_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7114_, 0, v_e_7093_);
                            v___x_7113_ = v_reuseFailAlloc_7114_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7093_);
                        v_val_7115_ = crate::leanh::lean_ctor_get(v_e_x3f_7111_, 0);
                        crate::leanh::lean_inc(v_val_7115_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_7111_, 1);
                        if v_isShared_7104_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7103_, 0, v_val_7115_);
                            v___x_7117_ = v___x_7103_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7118_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7118_, 0, v_val_7115_);
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
                    v_reuseFailAlloc_7126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7126_, 0, v_a_7120_);
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
    mut v_pre_7128_: *mut crate::leanh::LeanObject,
    mut v_post_7129_: *mut crate::leanh::LeanObject,
    mut v_e_7130_: *mut crate::leanh::LeanObject,
    mut v_a_7131_: *mut crate::leanh::LeanObject,
    mut v___y_7132_: *mut crate::leanh::LeanObject,
    mut v___y_7133_: *mut crate::leanh::LeanObject,
    mut v___y_7134_: *mut crate::leanh::LeanObject,
    mut v___y_7135_: *mut crate::leanh::LeanObject,
    mut v___y_7136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7137_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_7128_, v_post_7129_, v_e_7130_, v_a_7131_, v___y_7132_, v___y_7133_, v___y_7134_, v___y_7135_);
    crate::leanh::lean_dec(v___y_7135_);
    crate::leanh::lean_dec_ref(v___y_7134_);
    crate::leanh::lean_dec(v___y_7133_);
    crate::leanh::lean_dec_ref(v___y_7132_);
    crate::leanh::lean_dec(v_a_7131_);
    return v_res_7137_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(
    mut v_pre_7138_: *mut crate::leanh::LeanObject,
    mut v_post_7139_: *mut crate::leanh::LeanObject,
    mut v_sz_7140_: *mut crate::leanh::LeanObject,
    mut v_i_7141_: *mut crate::leanh::LeanObject,
    mut v_bs_7142_: *mut crate::leanh::LeanObject,
    mut v___y_7143_: *mut crate::leanh::LeanObject,
    mut v___y_7144_: *mut crate::leanh::LeanObject,
    mut v___y_7145_: *mut crate::leanh::LeanObject,
    mut v___y_7146_: *mut crate::leanh::LeanObject,
    mut v___y_7147_: *mut crate::leanh::LeanObject,
    mut v___y_7148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7149_: usize = 0;
    let mut v_i_boxed_7150_: usize = 0;
    let mut v_res_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7149_ = crate::leanh::lean_unbox_usize(v_sz_7140_);
    crate::leanh::lean_dec(v_sz_7140_);
    v_i_boxed_7150_ = crate::leanh::lean_unbox_usize(v_i_7141_);
    crate::leanh::lean_dec(v_i_7141_);
    v_res_7151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_7138_, v_post_7139_, v_sz_boxed_7149_, v_i_boxed_7150_, v_bs_7142_, v___y_7143_, v___y_7144_, v___y_7145_, v___y_7146_, v___y_7147_);
    crate::leanh::lean_dec(v___y_7147_);
    crate::leanh::lean_dec_ref(v___y_7146_);
    crate::leanh::lean_dec(v___y_7145_);
    crate::leanh::lean_dec_ref(v___y_7144_);
    crate::leanh::lean_dec(v___y_7143_);
    return v_res_7151_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(
    mut v_pre_7152_: *mut crate::leanh::LeanObject,
    mut v_post_7153_: *mut crate::leanh::LeanObject,
    mut v_x_7154_: *mut crate::leanh::LeanObject,
    mut v_x_7155_: *mut crate::leanh::LeanObject,
    mut v_x_7156_: *mut crate::leanh::LeanObject,
    mut v___y_7157_: *mut crate::leanh::LeanObject,
    mut v___y_7158_: *mut crate::leanh::LeanObject,
    mut v___y_7159_: *mut crate::leanh::LeanObject,
    mut v___y_7160_: *mut crate::leanh::LeanObject,
    mut v___y_7161_: *mut crate::leanh::LeanObject,
    mut v___y_7162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7163_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_7152_, v_post_7153_, v_x_7154_, v_x_7155_, v_x_7156_, v___y_7157_, v___y_7158_, v___y_7159_, v___y_7160_, v___y_7161_);
    crate::leanh::lean_dec(v___y_7161_);
    crate::leanh::lean_dec_ref(v___y_7160_);
    crate::leanh::lean_dec(v___y_7159_);
    crate::leanh::lean_dec_ref(v___y_7158_);
    crate::leanh::lean_dec(v___y_7157_);
    return v_res_7163_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(
    mut v_pre_7164_: *mut crate::leanh::LeanObject,
    mut v_post_7165_: *mut crate::leanh::LeanObject,
    mut v_e_7166_: *mut crate::leanh::LeanObject,
    mut v_a_7167_: *mut crate::leanh::LeanObject,
    mut v___y_7168_: *mut crate::leanh::LeanObject,
    mut v___y_7169_: *mut crate::leanh::LeanObject,
    mut v___y_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
    mut v___y_7172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7173_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_7164_, v_post_7165_, v_e_7166_, v_a_7167_, v___y_7168_, v___y_7169_, v___y_7170_, v___y_7171_);
    crate::leanh::lean_dec(v___y_7171_);
    crate::leanh::lean_dec_ref(v___y_7170_);
    crate::leanh::lean_dec(v___y_7169_);
    crate::leanh::lean_dec_ref(v___y_7168_);
    crate::leanh::lean_dec(v_a_7167_);
    return v_res_7173_;
}
pub unsafe fn l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(
    mut v_input_7174_: *mut crate::leanh::LeanObject,
    mut v_pre_7175_: *mut crate::leanh::LeanObject,
    mut v_post_7176_: *mut crate::leanh::LeanObject,
    mut v___y_7177_: *mut crate::leanh::LeanObject,
    mut v___y_7178_: *mut crate::leanh::LeanObject,
    mut v___y_7179_: *mut crate::leanh::LeanObject,
    mut v___y_7180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7191_: u8 = 0;
    let mut v___x_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7195_: u8 = 0;
    let mut v_unused_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7182_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once), _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
                v___x_7183_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(crate::leanh::lean_box(0), v___x_7182_, v___y_7177_, v___y_7178_, v___y_7179_, v___y_7180_);
                v_a_7184_ = crate::leanh::lean_ctor_get(v___x_7183_, 0);
                crate::leanh::lean_inc(v_a_7184_);
                crate::leanh::lean_dec_ref(v___x_7183_);
                v___x_7185_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_7175_, v_post_7176_, v_input_7174_, v_a_7184_, v___y_7177_, v___y_7178_, v___y_7179_, v___y_7180_);
                if crate::leanh::lean_obj_tag(v___x_7185_) == 0 {
                    v_a_7186_ = crate::leanh::lean_ctor_get(v___x_7185_, 0);
                    crate::leanh::lean_inc(v_a_7186_);
                    crate::leanh::lean_dec_ref_known(v___x_7185_, 1);
                    v___x_7187_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_7187_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_7187_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_7187_, 2, v_a_7184_);
                    v___x_7188_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___lam__0(crate::leanh::lean_box(0), v___x_7187_, v___y_7177_, v___y_7178_, v___y_7179_, v___y_7180_);
                    v_isSharedCheck_7195_ = (!crate::leanh::lean_is_exclusive(v___x_7188_)) as u8;
                    if v_isSharedCheck_7195_ == 0 {
                        v_unused_7196_ = crate::leanh::lean_ctor_get(v___x_7188_, 0);
                        crate::leanh::lean_dec(v_unused_7196_);
                        v___x_7190_ = v___x_7188_;
                        v_isShared_7191_ = v_isSharedCheck_7195_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7188_);
                        v___x_7190_ = crate::leanh::lean_box(0);
                        v_isShared_7191_ = v_isSharedCheck_7195_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7184_);
                    return v___x_7185_;
                }
            }
            1 => {
                if v_isShared_7191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7190_, 0, v_a_7186_);
                    v___x_7193_ = v___x_7190_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7194_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 0, v_a_7186_);
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
    mut v_input_7197_: *mut crate::leanh::LeanObject,
    mut v_pre_7198_: *mut crate::leanh::LeanObject,
    mut v_post_7199_: *mut crate::leanh::LeanObject,
    mut v___y_7200_: *mut crate::leanh::LeanObject,
    mut v___y_7201_: *mut crate::leanh::LeanObject,
    mut v___y_7202_: *mut crate::leanh::LeanObject,
    mut v___y_7203_: *mut crate::leanh::LeanObject,
    mut v___y_7204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7205_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(
        v_input_7197_,
        v_pre_7198_,
        v_post_7199_,
        v___y_7200_,
        v___y_7201_,
        v___y_7202_,
        v___y_7203_,
    );
    crate::leanh::lean_dec(v___y_7203_);
    crate::leanh::lean_dec_ref(v___y_7202_);
    crate::leanh::lean_dec(v___y_7201_);
    crate::leanh::lean_dec_ref(v___y_7200_);
    return v_res_7205_;
}
pub unsafe fn l_Lean_Meta_Grind_replacePreMatchCond(
    mut v_e_7209_: *mut crate::leanh::LeanObject,
    mut v_a_7210_: *mut crate::leanh::LeanObject,
    mut v_a_7211_: *mut crate::leanh::LeanObject,
    mut v_a_7212_: *mut crate::leanh::LeanObject,
    mut v_a_7213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v_pre_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7233_: u8 = 0;
    let mut v___x_7234_: u8 = 0;
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7243_: u8 = 0;
    let mut v_a_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7247_: u8 = 0;
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7251_: u8 = 0;
    let mut v_a_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7255_: u8 = 0;
    let mut v___x_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7259_: u8 = 0;
    let mut v_a_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7263_: u8 = 0;
    let mut v___x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7267_: u8 = 0;
    let mut v_isSharedCheck_7268_: u8 = 0;
    let mut v_unused_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7215_ = l_Lean_Meta_Grind_replacePreMatchCond___closed__0;
                v___x_7216_ = lean_find_expr(v___x_7215_, v_e_7209_);
                if crate::leanh::lean_obj_tag(v___x_7216_) == 0 {
                    v___x_7217_ = 1;
                    v___x_7218_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_7218_, 0, v_e_7209_);
                    crate::leanh::lean_ctor_set(v___x_7218_, 1, v___x_7216_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_7218_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_7217_,
                    );
                    v___x_7219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7219_, 0, v___x_7218_);
                    return v___x_7219_;
                } else {
                    v_isSharedCheck_7268_ = (!crate::leanh::lean_is_exclusive(v___x_7216_)) as u8;
                    if v_isSharedCheck_7268_ == 0 {
                        v_unused_7269_ = crate::leanh::lean_ctor_get(v___x_7216_, 0);
                        crate::leanh::lean_dec(v_unused_7269_);
                        v___x_7221_ = v___x_7216_;
                        v_isShared_7222_ = v_isSharedCheck_7268_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7216_);
                        v___x_7221_ = crate::leanh::lean_box(0);
                        v_isShared_7222_ = v_isSharedCheck_7268_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pre_7223_ = l_Lean_Meta_Grind_replacePreMatchCond___closed__1;
                v___f_7224_ = l_Lean_Meta_Grind_replacePreMatchCond___closed__2;
                crate::leanh::lean_inc_ref(v_e_7209_);
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
                if crate::leanh::lean_obj_tag(v___x_7225_) == 0 {
                    v_a_7226_ = crate::leanh::lean_ctor_get(v___x_7225_, 0);
                    crate::leanh::lean_inc_n(v_a_7226_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_7225_, 1);
                    v___x_7227_ =
                        l_Lean_Meta_mkEqRefl(v_a_7226_, v_a_7210_, v_a_7211_, v_a_7212_, v_a_7213_);
                    if crate::leanh::lean_obj_tag(v___x_7227_) == 0 {
                        v_a_7228_ = crate::leanh::lean_ctor_get(v___x_7227_, 0);
                        crate::leanh::lean_inc(v_a_7228_);
                        crate::leanh::lean_dec_ref_known(v___x_7227_, 1);
                        crate::leanh::lean_inc(v_a_7226_);
                        v___x_7229_ = l_Lean_Meta_mkEq(
                            v_e_7209_, v_a_7226_, v_a_7210_, v_a_7211_, v_a_7212_, v_a_7213_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7229_) == 0 {
                            v_a_7230_ = crate::leanh::lean_ctor_get(v___x_7229_, 0);
                            v_isSharedCheck_7243_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7229_)) as u8;
                            if v_isSharedCheck_7243_ == 0 {
                                v___x_7232_ = v___x_7229_;
                                v_isShared_7233_ = v_isSharedCheck_7243_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7230_);
                                crate::leanh::lean_dec(v___x_7229_);
                                v___x_7232_ = crate::leanh::lean_box(0);
                                v_isShared_7233_ = v_isSharedCheck_7243_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7228_);
                            crate::leanh::lean_dec(v_a_7226_);
                            crate::leanh::lean_del_object(v___x_7221_);
                            v_a_7244_ = crate::leanh::lean_ctor_get(v___x_7229_, 0);
                            v_isSharedCheck_7251_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7229_)) as u8;
                            if v_isSharedCheck_7251_ == 0 {
                                v___x_7246_ = v___x_7229_;
                                v_isShared_7247_ = v_isSharedCheck_7251_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7244_);
                                crate::leanh::lean_dec(v___x_7229_);
                                v___x_7246_ = crate::leanh::lean_box(0);
                                v_isShared_7247_ = v_isSharedCheck_7251_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7226_);
                        crate::leanh::lean_del_object(v___x_7221_);
                        crate::leanh::lean_dec_ref(v_e_7209_);
                        v_a_7252_ = crate::leanh::lean_ctor_get(v___x_7227_, 0);
                        v_isSharedCheck_7259_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7227_)) as u8;
                        if v_isSharedCheck_7259_ == 0 {
                            v___x_7254_ = v___x_7227_;
                            v_isShared_7255_ = v_isSharedCheck_7259_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7252_);
                            crate::leanh::lean_dec(v___x_7227_);
                            v___x_7254_ = crate::leanh::lean_box(0);
                            v_isShared_7255_ = v_isSharedCheck_7259_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7221_);
                    crate::leanh::lean_dec_ref(v_e_7209_);
                    v_a_7260_ = crate::leanh::lean_ctor_get(v___x_7225_, 0);
                    v_isSharedCheck_7267_ = (!crate::leanh::lean_is_exclusive(v___x_7225_)) as u8;
                    if v_isSharedCheck_7267_ == 0 {
                        v___x_7262_ = v___x_7225_;
                        v_isShared_7263_ = v_isSharedCheck_7267_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7260_);
                        crate::leanh::lean_dec(v___x_7225_);
                        v___x_7262_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_7221_, 0, v___x_7235_);
                    v___x_7237_ = v___x_7221_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7242_, 0, v___x_7235_);
                    v___x_7237_ = v_reuseFailAlloc_7242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7238_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_7238_, 0, v_a_7226_);
                crate::leanh::lean_ctor_set(v___x_7238_, 1, v___x_7237_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7238_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_7234_,
                );
                if v_isShared_7233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7232_, 0, v___x_7238_);
                    v___x_7240_ = v___x_7232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7241_, 0, v___x_7238_);
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
                    v_reuseFailAlloc_7250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 0, v_a_7244_);
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
                    v_reuseFailAlloc_7258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7258_, 0, v_a_7252_);
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
                    v_reuseFailAlloc_7266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7266_, 0, v_a_7260_);
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
    mut v_e_7270_: *mut crate::leanh::LeanObject,
    mut v_a_7271_: *mut crate::leanh::LeanObject,
    mut v_a_7272_: *mut crate::leanh::LeanObject,
    mut v_a_7273_: *mut crate::leanh::LeanObject,
    mut v_a_7274_: *mut crate::leanh::LeanObject,
    mut v_a_7275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7276_ = l_Lean_Meta_Grind_replacePreMatchCond(
        v_e_7270_, v_a_7271_, v_a_7272_, v_a_7273_, v_a_7274_,
    );
    crate::leanh::lean_dec(v_a_7274_);
    crate::leanh::lean_dec_ref(v_a_7273_);
    crate::leanh::lean_dec(v_a_7272_);
    crate::leanh::lean_dec_ref(v_a_7271_);
    return v_res_7276_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(
    mut v_00_u03b1_7277_: *mut crate::leanh::LeanObject,
    mut v_x_7278_: *mut crate::leanh::LeanObject,
    mut v___y_7279_: *mut crate::leanh::LeanObject,
    mut v___y_7280_: *mut crate::leanh::LeanObject,
    mut v___y_7281_: *mut crate::leanh::LeanObject,
    mut v___y_7282_: *mut crate::leanh::LeanObject,
    mut v___y_7283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7285_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_7278_, v___y_7279_, v___y_7280_, v___y_7281_, v___y_7282_, v___y_7283_);
    return v___x_7285_;
}
pub unsafe fn l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b1_7286_: *mut crate::leanh::LeanObject,
    mut v_x_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
    mut v___y_7291_: *mut crate::leanh::LeanObject,
    mut v___y_7292_: *mut crate::leanh::LeanObject,
    mut v___y_7293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7294_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_7286_, v_x_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_);
    crate::leanh::lean_dec(v___y_7292_);
    crate::leanh::lean_dec_ref(v___y_7291_);
    crate::leanh::lean_dec(v___y_7290_);
    crate::leanh::lean_dec_ref(v___y_7289_);
    crate::leanh::lean_dec(v___y_7288_);
    return v_res_7294_;
}
pub unsafe fn l_Lean_Meta_Grind_isIte(mut v_e_7298_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: u8 = 0;
    v___x_7299_ = l_Lean_Meta_Grind_isIte___closed__1;
    v___x_7300_ = l_Lean_Expr_isAppOf(v_e_7298_, v___x_7299_);
    if v___x_7300_ == 0 {
        return v___x_7300_;
    } else {
        let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7303_: u8 = 0;
        v___x_7301_ = crate::leanh::lean_unsigned_to_nat(5);
        v___x_7302_ = l_Lean_Expr_getAppNumArgs(v_e_7298_);
        v___x_7303_ = lean_nat_dec_le(v___x_7301_, v___x_7302_);
        crate::leanh::lean_dec(v___x_7302_);
        return v___x_7303_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isIte___boxed(
    mut v_e_7304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7305_: u8 = 0;
    let mut v_r_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7305_ = l_Lean_Meta_Grind_isIte(v_e_7304_);
    crate::leanh::lean_dec_ref(v_e_7304_);
    v_r_7306_ = crate::leanh::lean_box((v_res_7305_) as usize);
    return v_r_7306_;
}
pub unsafe fn l_Lean_Meta_Grind_isDIte(mut v_e_7310_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: u8 = 0;
    v___x_7311_ = l_Lean_Meta_Grind_isDIte___closed__1;
    v___x_7312_ = l_Lean_Expr_isAppOf(v_e_7310_, v___x_7311_);
    if v___x_7312_ == 0 {
        return v___x_7312_;
    } else {
        let mut v___x_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7315_: u8 = 0;
        v___x_7313_ = crate::leanh::lean_unsigned_to_nat(5);
        v___x_7314_ = l_Lean_Expr_getAppNumArgs(v_e_7310_);
        v___x_7315_ = lean_nat_dec_le(v___x_7313_, v___x_7314_);
        crate::leanh::lean_dec(v___x_7314_);
        return v___x_7315_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isDIte___boxed(
    mut v_e_7316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7317_: u8 = 0;
    let mut v_r_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7317_ = l_Lean_Meta_Grind_isDIte(v_e_7316_);
    crate::leanh::lean_dec_ref(v_e_7316_);
    v_r_7318_ = crate::leanh::lean_box((v_res_7317_) as usize);
    return v_r_7318_;
}
pub unsafe fn l_Lean_Meta_Grind_getBinOp(
    mut v_e_7319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7320_: u8 = 0;
    v___x_7320_ = l_Lean_Expr_isApp(v_e_7319_);
    if v___x_7320_ == 0 {
        let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7321_ = crate::leanh::lean_box(0);
        return v___x_7321_;
    } else {
        let mut v_f_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7323_: u8 = 0;
        v_f_7322_ = l_Lean_Expr_appFn_x21(v_e_7319_);
        v___x_7323_ = l_Lean_Expr_isApp(v_f_7322_);
        if v___x_7323_ == 0 {
            let mut v___x_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_f_7322_);
            v___x_7324_ = crate::leanh::lean_box(0);
            return v___x_7324_;
        } else {
            let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7325_ = l_Lean_Expr_appFn_x21(v_f_7322_);
            crate::leanh::lean_dec_ref(v_f_7322_);
            v___x_7326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_7326_, 0, v___x_7325_);
            return v___x_7326_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getBinOp___boxed(
    mut v_e_7327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7328_ = l_Lean_Meta_Grind_getBinOp(v_e_7327_);
    crate::leanh::lean_dec_ref(v_e_7327_);
    return v_res_7328_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Util(builtin);
}
