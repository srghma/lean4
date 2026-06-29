// Lean compiler output
// Module: Lean.Meta.Structure
// Imports: Lean.AddDecl Lean.Meta.AppBuilder Lean.Structure Lean.Meta.Transform
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv, lean_expr_instantiate_rev,
    lean_expr_instantiate1, lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub, lean_whnf,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
    l_List_lengthTR___redArg, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_Core_instantiateValueLevelParams,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_empty, l_Lean_NameSet_insert};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_InductiveVal_numCtors,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_hasUnsafe, l_Lean_Environment_setExporting,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_BinderInfo_isInstImplicit,
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_bindingBody_x21, l_Lean_Expr_bindingDomain_x21,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar,
    l_Lean_Expr_inferImplicit, l_Lean_Expr_isApp, l_Lean_Expr_isConst, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isForall, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_Expr_sort___override, l_Lean_Expr_updateForallBinderInfos, l_Lean_ExprStructEq_beq,
    l_Lean_ExprStructEq_hash, l_Lean_instInhabitedExpr, l_Lean_mkAppN,
    lean_expr_consume_type_annotations, lean_is_out_param,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkForall, l_Lean_LocalContext_mkLambda, l_Lean_LocalContext_setBinderInfo,
    l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_inferType___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_isDefEq___boxed,
    l_Lean_Meta_isExprDefEqGuarded, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkFreshLevelMVarsFor___boxed, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProp, l_Lean_Meta_isPropFormerType};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::MonadEnv::{l_Lean_getConstInfo___redArg, l_Lean_isInductiveCore_x3f};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ProjFns::{
    l_Lean_Environment_getProjectionFnInfo_x3f, l_Lean_addProjectionFnInfo,
};
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
use crate::r#gen::Lean::Structure::{
    initialize_Lean_Structure, l_Lean_isStructure, runtime_initialize_Lean_Structure,
};
pub static l_Lean_Meta_getStructureName___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Meta_getStructureName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getStructureName___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getStructureName___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getStructureName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getStructureName___closed__2_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 115, 116, 114, 117, 99, 116, 117, 114,
            101, 0,
        ],
    };
static mut l_Lean_Meta_getStructureName___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getStructureName___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getStructureName___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getStructureName___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getStructureName___closed__4_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101,
            0,
        ],
    };
static mut l_Lean_Meta_getStructureName___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getStructureName___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getStructureName___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getStructureName___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 96, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [96, 32, 102, 111, 114, 32, 96, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [96, 44, 32, 110, 111, 116, 32, 101, 110, 111, 117, 103, 104, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 102, 105, 101, 108, 100, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [96, 32, 102, 111, 114, 32, 116, 104, 101, 32, 39, 80, 114, 111, 112, 39, 45, 118, 97, 108, 117, 101, 100, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [96, 44, 32, 102, 105, 101, 108, 100, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 32, 112, 114, 111, 111, 102, 44, 32, 98, 117, 116, 32, 105, 116, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [96, 44, 32, 116, 111, 111, 32, 109, 97, 110, 121, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 118, 101, 114, 114, 105, 100, 101, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkProjections___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 101, 108, 102, 0],
    };
static mut l_Lean_Meta_mkProjections___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkProjections___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15836239757596156536 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkProjections___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkProjections___lam__1___closed__2_value: crate::leanh::LeanStringObject<
    32,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 103, 101, 110, 101, 114, 97, 116, 105,
        111, 110, 32, 102, 97, 105, 108, 101, 100, 44, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_mkProjections___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkProjections___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkProjections___lam__1___closed__4_value: crate::leanh::LeanStringObject<
    38,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        96, 32, 105, 115, 32, 97, 110, 32, 105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32,
        105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Meta_mkProjections___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkProjections___lam__1___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105,
        118, 101, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkProjections___lam__2___closed__0_value: crate::leanh::LeanStringObject<
    34,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 112, 114, 111,
        106, 101, 99, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_mkProjections___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkProjections___lam__2___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkProjections___lam__2___closed__2_value: crate::leanh::LeanStringObject<
    41,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        96, 44, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 101, 120, 97,
        99, 116, 108, 121, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
        114, 0,
    ],
};
static mut l_Lean_Meta_mkProjections___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_mkProjections___lam__2___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkProjections___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkProjections___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkProjections___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkProjections___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_mkProjections___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_mkProjections___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_mkProjections___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_mkProjections___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProjections___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_etaStructReduce___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
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
static mut l_Lean_Meta_etaStructReduce___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_etaStructReduce___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 114, 97, 110, 115, 102, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_etaStructReduce___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_etaStructReduce___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_etaStructReduce___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_etaStructReduce___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,6041859491766292191 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 116, 114, 117, 99, 116, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116,
        101, 83, 116, 114, 117, 99, 116, 68, 101, 102, 97, 117, 108, 116, 86, 97, 108, 117, 101,
        70, 110, 63, 0,
    ],
};
static mut l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2_value:
    crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 117, 115, 46, 108, 101, 110, 103, 116, 104, 32, 61, 61, 32, 99, 105, 110, 102, 111,
        46, 108, 101, 118, 101, 108, 80, 97, 114, 97, 109, 115, 46, 108, 101, 110, 103, 116, 104,
        10, 32, 32, 0,
    ],
};
static mut l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(
    mut v_msgData_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4109_ = lean_st_ref_get(v___y_4107_);
    v_env_4110_ = crate::leanh::lean_ctor_get(v___x_4109_, 0);
    crate::leanh::lean_inc_ref(v_env_4110_);
    crate::leanh::lean_dec(v___x_4109_);
    v___x_4111_ = lean_st_ref_get(v___y_4105_);
    v_mctx_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4112_);
    crate::leanh::lean_dec(v___x_4111_);
    v_lctx_4113_ = crate::leanh::lean_ctor_get(v___y_4104_, 2);
    v_options_4114_ = crate::leanh::lean_ctor_get(v___y_4106_, 2);
    crate::leanh::lean_inc_ref(v_options_4114_);
    crate::leanh::lean_inc_ref(v_lctx_4113_);
    v___x_4115_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4115_, 0, v_env_4110_);
    crate::leanh::lean_ctor_set(v___x_4115_, 1, v_mctx_4112_);
    crate::leanh::lean_ctor_set(v___x_4115_, 2, v_lctx_4113_);
    crate::leanh::lean_ctor_set(v___x_4115_, 3, v_options_4114_);
    v___x_4116_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4116_, 0, v___x_4115_);
    crate::leanh::lean_ctor_set(v___x_4116_, 1, v_msgData_4103_);
    v___x_4117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4116_);
    return v___x_4117_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0___boxed(
    mut v_msgData_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msgData_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
    crate::leanh::lean_dec(v___y_4122_);
    crate::leanh::lean_dec_ref(v___y_4121_);
    crate::leanh::lean_dec(v___y_4120_);
    crate::leanh::lean_dec_ref(v___y_4119_);
    return v_res_4124_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
    mut v_msg_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4131_ = crate::leanh::lean_ctor_get(v___y_4128_, 5);
                v___x_4132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getStructureName_spec__0_spec__0(v_msg_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
                v_a_4133_ = crate::leanh::lean_ctor_get(v___x_4132_, 0);
                v_isSharedCheck_4141_ = (!crate::leanh::lean_is_exclusive(v___x_4132_)) as u8;
                if v_isSharedCheck_4141_ == 0 {
                    v___x_4135_ = v___x_4132_;
                    v_isShared_4136_ = v_isSharedCheck_4141_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4133_);
                    crate::leanh::lean_dec(v___x_4132_);
                    v___x_4135_ = crate::leanh::lean_box(0);
                    v_isShared_4136_ = v_isSharedCheck_4141_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4131_);
                v___x_4137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4137_, 0, v_ref_4131_);
                crate::leanh::lean_ctor_set(v___x_4137_, 1, v_a_4133_);
                if v_isShared_4136_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4135_, 1);
                    crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4137_);
                    v___x_4139_ = v___x_4135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4137_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg___boxed(
    mut v_msg_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
        v_msg_4142_,
        v___y_4143_,
        v___y_4144_,
        v___y_4145_,
        v___y_4146_,
    );
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v___y_4145_);
    crate::leanh::lean_dec(v___y_4144_);
    crate::leanh::lean_dec_ref(v___y_4143_);
    return v_res_4148_;
}
pub unsafe fn _init_l_Lean_Meta_getStructureName___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lean_Meta_getStructureName___closed__0;
    v___x_4151_ = l_Lean_stringToMessageData(v___x_4150_);
    return v___x_4151_;
}
pub unsafe fn _init_l_Lean_Meta_getStructureName___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ = l_Lean_Meta_getStructureName___closed__2;
    v___x_4154_ = l_Lean_stringToMessageData(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l_Lean_Meta_getStructureName___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = l_Lean_Meta_getStructureName___closed__4;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_Lean_Meta_getStructureName(
    mut v_struct_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4164_ = l_Lean_Expr_getAppFn(v_struct_4158_);
                if crate::leanh::lean_obj_tag(v___x_4164_) == 4 {
                    v_declName_4165_ = crate::leanh::lean_ctor_get(v___x_4164_, 0);
                    crate::leanh::lean_inc_n(v_declName_4165_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4164_, 2);
                    v___x_4166_ = lean_st_ref_get(v_a_4162_);
                    v_env_4167_ = crate::leanh::lean_ctor_get(v___x_4166_, 0);
                    crate::leanh::lean_inc_ref(v_env_4167_);
                    crate::leanh::lean_dec(v___x_4166_);
                    v___x_4168_ = l_Lean_isStructure(v_env_4167_, v_declName_4165_);
                    if v___x_4168_ == 0 {
                        v___x_4169_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__1_once),
                            _init_l_Lean_Meta_getStructureName___closed__1,
                        );
                        v___x_4170_ = l_Lean_MessageData_ofConstName(v_declName_4165_, v___x_4168_);
                        v___x_4171_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4171_, 0, v___x_4169_);
                        crate::leanh::lean_ctor_set(v___x_4171_, 1, v___x_4170_);
                        v___x_4172_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__3_once),
                            _init_l_Lean_Meta_getStructureName___closed__3,
                        );
                        v___x_4173_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4173_, 0, v___x_4171_);
                        crate::leanh::lean_ctor_set(v___x_4173_, 1, v___x_4172_);
                        v___x_4174_ =
                            l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
                                v___x_4173_,
                                v_a_4159_,
                                v_a_4160_,
                                v_a_4161_,
                                v_a_4162_,
                            );
                        v_a_4175_ = crate::leanh::lean_ctor_get(v___x_4174_, 0);
                        v_isSharedCheck_4182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4174_)) as u8;
                        if v_isSharedCheck_4182_ == 0 {
                            v___x_4177_ = v___x_4174_;
                            v_isShared_4178_ = v_isSharedCheck_4182_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4175_);
                            crate::leanh::lean_dec(v___x_4174_);
                            v___x_4177_ = crate::leanh::lean_box(0);
                            v_isShared_4178_ = v_isSharedCheck_4182_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4183_, 0, v_declName_4165_);
                        return v___x_4183_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4164_);
                    v___x_4184_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__5_once),
                        _init_l_Lean_Meta_getStructureName___closed__5,
                    );
                    v___x_4185_ =
                        l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
                            v___x_4184_,
                            v_a_4159_,
                            v_a_4160_,
                            v_a_4161_,
                            v_a_4162_,
                        );
                    return v___x_4185_;
                }
            }
            1 => {
                if v_isShared_4178_ == 0 {
                    v___x_4180_ = v___x_4177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getStructureName___boxed(
    mut v_struct_4186_: *mut crate::leanh::LeanObject,
    mut v_a_4187_: *mut crate::leanh::LeanObject,
    mut v_a_4188_: *mut crate::leanh::LeanObject,
    mut v_a_4189_: *mut crate::leanh::LeanObject,
    mut v_a_4190_: *mut crate::leanh::LeanObject,
    mut v_a_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4192_ =
        l_Lean_Meta_getStructureName(v_struct_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
    crate::leanh::lean_dec(v_a_4190_);
    crate::leanh::lean_dec_ref(v_a_4189_);
    crate::leanh::lean_dec(v_a_4188_);
    crate::leanh::lean_dec_ref(v_a_4187_);
    crate::leanh::lean_dec_ref(v_struct_4186_);
    return v_res_4192_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(
    mut v_00_u03b1_4193_: *mut crate::leanh::LeanObject,
    mut v_msg_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
        v_msg_4194_,
        v___y_4195_,
        v___y_4196_,
        v___y_4197_,
        v___y_4198_,
    );
    return v___x_4200_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___boxed(
    mut v_00_u03b1_4201_: *mut crate::leanh::LeanObject,
    mut v_msg_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4208_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0(
        v_00_u03b1_4201_,
        v_msg_4202_,
        v___y_4203_,
        v___y_4204_,
        v___y_4205_,
        v___y_4206_,
    );
    crate::leanh::lean_dec(v___y_4206_);
    crate::leanh::lean_dec_ref(v___y_4205_);
    crate::leanh::lean_dec(v___y_4204_);
    crate::leanh::lean_dec_ref(v___y_4203_);
    return v_res_4208_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(
    mut v_name_4209_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4210_: *mut crate::leanh::LeanObject,
    mut v_type_4211_: *mut crate::leanh::LeanObject,
    mut v_value_4212_: *mut crate::leanh::LeanObject,
    mut v_hints_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: u8 = 0;
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: u8 = 0;
    let mut v_env_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4216_ = lean_st_ref_get(v___y_4214_);
                v_env_4228_ = crate::leanh::lean_ctor_get(v___x_4216_, 0);
                crate::leanh::lean_inc_ref_n(v_env_4228_, 2);
                crate::leanh::lean_dec(v___x_4216_);
                v___x_4229_ = l_Lean_Environment_hasUnsafe(v_env_4228_, v_type_4211_);
                if v___x_4229_ == 0 {
                    v___x_4230_ = l_Lean_Environment_hasUnsafe(v_env_4228_, v_value_4212_);
                    v___y_4225_ = v___x_4230_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_4228_);
                    v___y_4225_ = v___x_4229_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_name_4209_);
                v___x_4219_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4219_, 0, v_name_4209_);
                crate::leanh::lean_ctor_set(v___x_4219_, 1, v_levelParams_4210_);
                crate::leanh::lean_ctor_set(v___x_4219_, 2, v_type_4211_);
                v___x_4220_ = crate::leanh::lean_box(0);
                v___x_4221_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4221_, 0, v_name_4209_);
                crate::leanh::lean_ctor_set(v___x_4221_, 1, v___x_4220_);
                v___x_4222_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4222_, 0, v___x_4219_);
                crate::leanh::lean_ctor_set(v___x_4222_, 1, v_value_4212_);
                crate::leanh::lean_ctor_set(v___x_4222_, 2, v_hints_4213_);
                crate::leanh::lean_ctor_set(v___x_4222_, 3, v___x_4221_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4222_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4218_,
                );
                v___x_4223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4223_, 0, v___x_4222_);
                return v___x_4223_;
            }
            2 => {
                if v___y_4225_ == 0 {
                    v___x_4226_ = 1;
                    v___y_4218_ = v___x_4226_;
                    state = 1;
                    continue;
                } else {
                    v___x_4227_ = 0;
                    v___y_4218_ = v___x_4227_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg___boxed(
    mut v_name_4231_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4232_: *mut crate::leanh::LeanObject,
    mut v_type_4233_: *mut crate::leanh::LeanObject,
    mut v_value_4234_: *mut crate::leanh::LeanObject,
    mut v_hints_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4238_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(
            v_name_4231_,
            v_levelParams_4232_,
            v_type_4233_,
            v_value_4234_,
            v_hints_4235_,
            v___y_4236_,
        );
    crate::leanh::lean_dec(v___y_4236_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(
    mut v_name_4239_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4240_: *mut crate::leanh::LeanObject,
    mut v_type_4241_: *mut crate::leanh::LeanObject,
    mut v_value_4242_: *mut crate::leanh::LeanObject,
    mut v_hints_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4249_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(
            v_name_4239_,
            v_levelParams_4240_,
            v_type_4241_,
            v_value_4242_,
            v_hints_4243_,
            v___y_4247_,
        );
    return v___x_4249_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___boxed(
    mut v_name_4250_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4251_: *mut crate::leanh::LeanObject,
    mut v_type_4252_: *mut crate::leanh::LeanObject,
    mut v_value_4253_: *mut crate::leanh::LeanObject,
    mut v_hints_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4(
        v_name_4250_,
        v_levelParams_4251_,
        v_type_4252_,
        v_value_4253_,
        v_hints_4254_,
        v___y_4255_,
        v___y_4256_,
        v___y_4257_,
        v___y_4258_,
    );
    crate::leanh::lean_dec(v___y_4258_);
    crate::leanh::lean_dec_ref(v___y_4257_);
    crate::leanh::lean_dec(v___y_4256_);
    crate::leanh::lean_dec_ref(v___y_4255_);
    return v_res_4260_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(
    mut v_k_4261_: *mut crate::leanh::LeanObject,
    mut v_b_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4266_);
    crate::leanh::lean_inc_ref(v___y_4265_);
    crate::leanh::lean_inc(v___y_4264_);
    crate::leanh::lean_inc_ref(v___y_4263_);
    v___x_4268_ = crate::leanh::lean_apply_6(
        v_k_4261_,
        v_b_4262_,
        v___y_4263_,
        v___y_4264_,
        v___y_4265_,
        v___y_4266_,
        crate::leanh::lean_box(0),
    );
    return v___x_4268_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed(
    mut v_k_4269_: *mut crate::leanh::LeanObject,
    mut v_b_4270_: *mut crate::leanh::LeanObject,
    mut v___y_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4276_ =
        l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0(
            v_k_4269_,
            v_b_4270_,
            v___y_4271_,
            v___y_4272_,
            v___y_4273_,
            v___y_4274_,
        );
    crate::leanh::lean_dec(v___y_4274_);
    crate::leanh::lean_dec_ref(v___y_4273_);
    crate::leanh::lean_dec(v___y_4272_);
    crate::leanh::lean_dec_ref(v___y_4271_);
    return v_res_4276_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(
    mut v_name_4277_: *mut crate::leanh::LeanObject,
    mut v_bi_4278_: u8,
    mut v_type_4279_: *mut crate::leanh::LeanObject,
    mut v_k_4280_: *mut crate::leanh::LeanObject,
    mut v_kind_4281_: u8,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v_a_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4300_: u8 = 0;
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4287_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_4287_, 0, v_k_4280_);
                v___x_4288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4277_,
                    v_bi_4278_,
                    v_type_4279_,
                    v___f_4287_,
                    v_kind_4281_,
                    v___y_4282_,
                    v___y_4283_,
                    v___y_4284_,
                    v___y_4285_,
                );
                if crate::leanh::lean_obj_tag(v___x_4288_) == 0 {
                    v_a_4289_ = crate::leanh::lean_ctor_get(v___x_4288_, 0);
                    v_isSharedCheck_4296_ = (!crate::leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4296_ == 0 {
                        v___x_4291_ = v___x_4288_;
                        v_isShared_4292_ = v_isSharedCheck_4296_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4289_);
                        crate::leanh::lean_dec(v___x_4288_);
                        v___x_4291_ = crate::leanh::lean_box(0);
                        v_isShared_4292_ = v_isSharedCheck_4296_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4297_ = crate::leanh::lean_ctor_get(v___x_4288_, 0);
                    v_isSharedCheck_4304_ = (!crate::leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4304_ == 0 {
                        v___x_4299_ = v___x_4288_;
                        v_isShared_4300_ = v_isSharedCheck_4304_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4297_);
                        crate::leanh::lean_dec(v___x_4288_);
                        v___x_4299_ = crate::leanh::lean_box(0);
                        v_isShared_4300_ = v_isSharedCheck_4304_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4292_ == 0 {
                    v___x_4294_ = v___x_4291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
                    v___x_4294_ = v_reuseFailAlloc_4295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4294_;
            }
            3 => {
                if v_isShared_4300_ == 0 {
                    v___x_4302_ = v___x_4299_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
                    v___x_4302_ = v_reuseFailAlloc_4303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg___boxed(
    mut v_name_4305_: *mut crate::leanh::LeanObject,
    mut v_bi_4306_: *mut crate::leanh::LeanObject,
    mut v_type_4307_: *mut crate::leanh::LeanObject,
    mut v_k_4308_: *mut crate::leanh::LeanObject,
    mut v_kind_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
    mut v___y_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4315_: u8 = 0;
    let mut v_kind_boxed_4316_: u8 = 0;
    let mut v_res_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4315_ = (crate::leanh::lean_unbox(v_bi_4306_) as u8);
    v_kind_boxed_4316_ = (crate::leanh::lean_unbox(v_kind_4309_) as u8);
    v_res_4317_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(
        v_name_4305_,
        v_bi_boxed_4315_,
        v_type_4307_,
        v_k_4308_,
        v_kind_boxed_4316_,
        v___y_4310_,
        v___y_4311_,
        v___y_4312_,
        v___y_4313_,
    );
    crate::leanh::lean_dec(v___y_4313_);
    crate::leanh::lean_dec_ref(v___y_4312_);
    crate::leanh::lean_dec(v___y_4311_);
    crate::leanh::lean_dec_ref(v___y_4310_);
    return v_res_4317_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(
    mut v_00_u03b1_4318_: *mut crate::leanh::LeanObject,
    mut v_name_4319_: *mut crate::leanh::LeanObject,
    mut v_bi_4320_: u8,
    mut v_type_4321_: *mut crate::leanh::LeanObject,
    mut v_k_4322_: *mut crate::leanh::LeanObject,
    mut v_kind_4323_: u8,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4329_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(
        v_name_4319_,
        v_bi_4320_,
        v_type_4321_,
        v_k_4322_,
        v_kind_4323_,
        v___y_4324_,
        v___y_4325_,
        v___y_4326_,
        v___y_4327_,
    );
    return v___x_4329_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___boxed(
    mut v_00_u03b1_4330_: *mut crate::leanh::LeanObject,
    mut v_name_4331_: *mut crate::leanh::LeanObject,
    mut v_bi_4332_: *mut crate::leanh::LeanObject,
    mut v_type_4333_: *mut crate::leanh::LeanObject,
    mut v_k_4334_: *mut crate::leanh::LeanObject,
    mut v_kind_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4341_: u8 = 0;
    let mut v_kind_boxed_4342_: u8 = 0;
    let mut v_res_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4341_ = (crate::leanh::lean_unbox(v_bi_4332_) as u8);
    v_kind_boxed_4342_ = (crate::leanh::lean_unbox(v_kind_4335_) as u8);
    v_res_4343_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9(
        v_00_u03b1_4330_,
        v_name_4331_,
        v_bi_boxed_4341_,
        v_type_4333_,
        v_k_4334_,
        v_kind_boxed_4342_,
        v___y_4336_,
        v___y_4337_,
        v___y_4338_,
        v___y_4339_,
    );
    crate::leanh::lean_dec(v___y_4339_);
    crate::leanh::lean_dec_ref(v___y_4338_);
    crate::leanh::lean_dec(v___y_4337_);
    crate::leanh::lean_dec_ref(v___y_4336_);
    return v_res_4343_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(
    mut v_k_4344_: *mut crate::leanh::LeanObject,
    mut v_b_4345_: *mut crate::leanh::LeanObject,
    mut v_c_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4350_);
    crate::leanh::lean_inc_ref(v___y_4349_);
    crate::leanh::lean_inc(v___y_4348_);
    crate::leanh::lean_inc_ref(v___y_4347_);
    v___x_4352_ = crate::leanh::lean_apply_7(
        v_k_4344_,
        v_b_4345_,
        v_c_4346_,
        v___y_4347_,
        v___y_4348_,
        v___y_4349_,
        v___y_4350_,
        crate::leanh::lean_box(0),
    );
    return v___x_4352_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed(
    mut v_k_4353_: *mut crate::leanh::LeanObject,
    mut v_b_4354_: *mut crate::leanh::LeanObject,
    mut v_c_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0(v_k_4353_, v_b_4354_, v_c_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
    crate::leanh::lean_dec(v___y_4359_);
    crate::leanh::lean_dec_ref(v___y_4358_);
    crate::leanh::lean_dec(v___y_4357_);
    crate::leanh::lean_dec_ref(v___y_4356_);
    return v_res_4361_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(
    mut v_type_4362_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4363_: *mut crate::leanh::LeanObject,
    mut v_k_4364_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4365_: u8,
    mut v_whnfType_4366_: u8,
    mut v___y_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
    mut v___y_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_a_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4385_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4372_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4372_, 0, v_k_4364_);
                v___x_4373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_4362_,
                    v_maxFVars_x3f_4363_,
                    v___f_4372_,
                    v_cleanupAnnotations_4365_,
                    v_whnfType_4366_,
                    v___y_4367_,
                    v___y_4368_,
                    v___y_4369_,
                    v___y_4370_,
                );
                if crate::leanh::lean_obj_tag(v___x_4373_) == 0 {
                    v_a_4374_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                    v_isSharedCheck_4381_ = (!crate::leanh::lean_is_exclusive(v___x_4373_)) as u8;
                    if v_isSharedCheck_4381_ == 0 {
                        v___x_4376_ = v___x_4373_;
                        v_isShared_4377_ = v_isSharedCheck_4381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4374_);
                        crate::leanh::lean_dec(v___x_4373_);
                        v___x_4376_ = crate::leanh::lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4381_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4382_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                    v_isSharedCheck_4389_ = (!crate::leanh::lean_is_exclusive(v___x_4373_)) as u8;
                    if v_isSharedCheck_4389_ == 0 {
                        v___x_4384_ = v___x_4373_;
                        v_isShared_4385_ = v_isSharedCheck_4389_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4382_);
                        crate::leanh::lean_dec(v___x_4373_);
                        v___x_4384_ = crate::leanh::lean_box(0);
                        v_isShared_4385_ = v_isSharedCheck_4389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4377_ == 0 {
                    v___x_4379_ = v___x_4376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
                    v___x_4379_ = v_reuseFailAlloc_4380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4379_;
            }
            3 => {
                if v_isShared_4385_ == 0 {
                    v___x_4387_ = v___x_4384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
                    v___x_4387_ = v_reuseFailAlloc_4388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg___boxed(
    mut v_type_4390_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4391_: *mut crate::leanh::LeanObject,
    mut v_k_4392_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4393_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4400_: u8 = 0;
    let mut v_whnfType_boxed_4401_: u8 = 0;
    let mut v_res_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4400_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4393_) as u8);
    v_whnfType_boxed_4401_ = (crate::leanh::lean_unbox(v_whnfType_4394_) as u8);
    v_res_4402_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(
            v_type_4390_,
            v_maxFVars_x3f_4391_,
            v_k_4392_,
            v_cleanupAnnotations_boxed_4400_,
            v_whnfType_boxed_4401_,
            v___y_4395_,
            v___y_4396_,
            v___y_4397_,
            v___y_4398_,
        );
    crate::leanh::lean_dec(v___y_4398_);
    crate::leanh::lean_dec_ref(v___y_4397_);
    crate::leanh::lean_dec(v___y_4396_);
    crate::leanh::lean_dec_ref(v___y_4395_);
    return v_res_4402_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(
    mut v_00_u03b1_4403_: *mut crate::leanh::LeanObject,
    mut v_type_4404_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4405_: *mut crate::leanh::LeanObject,
    mut v_k_4406_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4407_: u8,
    mut v_whnfType_4408_: u8,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
    mut v___y_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(
            v_type_4404_,
            v_maxFVars_x3f_4405_,
            v_k_4406_,
            v_cleanupAnnotations_4407_,
            v_whnfType_4408_,
            v___y_4409_,
            v___y_4410_,
            v___y_4411_,
            v___y_4412_,
        );
    return v___x_4414_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___boxed(
    mut v_00_u03b1_4415_: *mut crate::leanh::LeanObject,
    mut v_type_4416_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4417_: *mut crate::leanh::LeanObject,
    mut v_k_4418_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4419_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
    mut v___y_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
    mut v___y_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4426_: u8 = 0;
    let mut v_whnfType_boxed_4427_: u8 = 0;
    let mut v_res_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4426_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4419_) as u8);
    v_whnfType_boxed_4427_ = (crate::leanh::lean_unbox(v_whnfType_4420_) as u8);
    v_res_4428_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10(
        v_00_u03b1_4415_,
        v_type_4416_,
        v_maxFVars_x3f_4417_,
        v_k_4418_,
        v_cleanupAnnotations_boxed_4426_,
        v_whnfType_boxed_4427_,
        v___y_4421_,
        v___y_4422_,
        v___y_4423_,
        v___y_4424_,
    );
    crate::leanh::lean_dec(v___y_4424_);
    crate::leanh::lean_dec_ref(v___y_4423_);
    crate::leanh::lean_dec(v___y_4422_);
    crate::leanh::lean_dec_ref(v___y_4421_);
    return v_res_4428_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(
    mut v_lctx_4429_: *mut crate::leanh::LeanObject,
    mut v_localInsts_4430_: *mut crate::leanh::LeanObject,
    mut v_x_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4441_: u8 = 0;
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut v_a_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4437_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    crate::leanh::lean_box(0),
                    v_lctx_4429_,
                    v_localInsts_4430_,
                    v_x_4431_,
                    v___y_4432_,
                    v___y_4433_,
                    v___y_4434_,
                    v___y_4435_,
                );
                if crate::leanh::lean_obj_tag(v___x_4437_) == 0 {
                    v_a_4438_ = crate::leanh::lean_ctor_get(v___x_4437_, 0);
                    v_isSharedCheck_4445_ = (!crate::leanh::lean_is_exclusive(v___x_4437_)) as u8;
                    if v_isSharedCheck_4445_ == 0 {
                        v___x_4440_ = v___x_4437_;
                        v_isShared_4441_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4438_);
                        crate::leanh::lean_dec(v___x_4437_);
                        v___x_4440_ = crate::leanh::lean_box(0);
                        v_isShared_4441_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4446_ = crate::leanh::lean_ctor_get(v___x_4437_, 0);
                    v_isSharedCheck_4453_ = (!crate::leanh::lean_is_exclusive(v___x_4437_)) as u8;
                    if v_isSharedCheck_4453_ == 0 {
                        v___x_4448_ = v___x_4437_;
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4446_);
                        crate::leanh::lean_dec(v___x_4437_);
                        v___x_4448_ = crate::leanh::lean_box(0);
                        v_isShared_4449_ = v_isSharedCheck_4453_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4441_ == 0 {
                    v___x_4443_ = v___x_4440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
                    v___x_4443_ = v_reuseFailAlloc_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4443_;
            }
            3 => {
                if v_isShared_4449_ == 0 {
                    v___x_4451_ = v___x_4448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
                    v___x_4451_ = v_reuseFailAlloc_4452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg___boxed(
    mut v_lctx_4454_: *mut crate::leanh::LeanObject,
    mut v_localInsts_4455_: *mut crate::leanh::LeanObject,
    mut v_x_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
    mut v___y_4460_: *mut crate::leanh::LeanObject,
    mut v___y_4461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4462_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(
        v_lctx_4454_,
        v_localInsts_4455_,
        v_x_4456_,
        v___y_4457_,
        v___y_4458_,
        v___y_4459_,
        v___y_4460_,
    );
    crate::leanh::lean_dec(v___y_4460_);
    crate::leanh::lean_dec_ref(v___y_4459_);
    crate::leanh::lean_dec(v___y_4458_);
    crate::leanh::lean_dec_ref(v___y_4457_);
    return v_res_4462_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(
    mut v_00_u03b1_4463_: *mut crate::leanh::LeanObject,
    mut v_lctx_4464_: *mut crate::leanh::LeanObject,
    mut v_localInsts_4465_: *mut crate::leanh::LeanObject,
    mut v_x_4466_: *mut crate::leanh::LeanObject,
    mut v___y_4467_: *mut crate::leanh::LeanObject,
    mut v___y_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4472_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(
        v_lctx_4464_,
        v_localInsts_4465_,
        v_x_4466_,
        v___y_4467_,
        v___y_4468_,
        v___y_4469_,
        v___y_4470_,
    );
    return v___x_4472_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___boxed(
    mut v_00_u03b1_4473_: *mut crate::leanh::LeanObject,
    mut v_lctx_4474_: *mut crate::leanh::LeanObject,
    mut v_localInsts_4475_: *mut crate::leanh::LeanObject,
    mut v_x_4476_: *mut crate::leanh::LeanObject,
    mut v___y_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11(
        v_00_u03b1_4473_,
        v_lctx_4474_,
        v_localInsts_4475_,
        v_x_4476_,
        v___y_4477_,
        v___y_4478_,
        v___y_4479_,
        v___y_4480_,
    );
    crate::leanh::lean_dec(v___y_4480_);
    crate::leanh::lean_dec_ref(v___y_4479_);
    crate::leanh::lean_dec(v___y_4478_);
    crate::leanh::lean_dec_ref(v___y_4477_);
    return v_res_4482_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(
    mut v_ref_4483_: *mut crate::leanh::LeanObject,
    mut v_msg_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4502_: u8 = 0;
    let mut v_cancelTk_x3f_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4504_: u8 = 0;
    let mut v_inheritedTraceOptions_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4490_ = crate::leanh::lean_ctor_get(v___y_4487_, 0);
    v_fileMap_4491_ = crate::leanh::lean_ctor_get(v___y_4487_, 1);
    v_options_4492_ = crate::leanh::lean_ctor_get(v___y_4487_, 2);
    v_currRecDepth_4493_ = crate::leanh::lean_ctor_get(v___y_4487_, 3);
    v_maxRecDepth_4494_ = crate::leanh::lean_ctor_get(v___y_4487_, 4);
    v_ref_4495_ = crate::leanh::lean_ctor_get(v___y_4487_, 5);
    v_currNamespace_4496_ = crate::leanh::lean_ctor_get(v___y_4487_, 6);
    v_openDecls_4497_ = crate::leanh::lean_ctor_get(v___y_4487_, 7);
    v_initHeartbeats_4498_ = crate::leanh::lean_ctor_get(v___y_4487_, 8);
    v_maxHeartbeats_4499_ = crate::leanh::lean_ctor_get(v___y_4487_, 9);
    v_quotContext_4500_ = crate::leanh::lean_ctor_get(v___y_4487_, 10);
    v_currMacroScope_4501_ = crate::leanh::lean_ctor_get(v___y_4487_, 11);
    v_diag_4502_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4487_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4503_ = crate::leanh::lean_ctor_get(v___y_4487_, 12);
    v_suppressElabErrors_4504_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4487_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4505_ = crate::leanh::lean_ctor_get(v___y_4487_, 13);
    v_ref_4506_ = l_Lean_replaceRef(v_ref_4483_, v_ref_4495_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4505_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4503_);
    crate::leanh::lean_inc(v_currMacroScope_4501_);
    crate::leanh::lean_inc(v_quotContext_4500_);
    crate::leanh::lean_inc(v_maxHeartbeats_4499_);
    crate::leanh::lean_inc(v_initHeartbeats_4498_);
    crate::leanh::lean_inc(v_openDecls_4497_);
    crate::leanh::lean_inc(v_currNamespace_4496_);
    crate::leanh::lean_inc(v_maxRecDepth_4494_);
    crate::leanh::lean_inc(v_currRecDepth_4493_);
    crate::leanh::lean_inc_ref(v_options_4492_);
    crate::leanh::lean_inc_ref(v_fileMap_4491_);
    crate::leanh::lean_inc_ref(v_fileName_4490_);
    v___x_4507_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4507_, 0, v_fileName_4490_);
    crate::leanh::lean_ctor_set(v___x_4507_, 1, v_fileMap_4491_);
    crate::leanh::lean_ctor_set(v___x_4507_, 2, v_options_4492_);
    crate::leanh::lean_ctor_set(v___x_4507_, 3, v_currRecDepth_4493_);
    crate::leanh::lean_ctor_set(v___x_4507_, 4, v_maxRecDepth_4494_);
    crate::leanh::lean_ctor_set(v___x_4507_, 5, v_ref_4506_);
    crate::leanh::lean_ctor_set(v___x_4507_, 6, v_currNamespace_4496_);
    crate::leanh::lean_ctor_set(v___x_4507_, 7, v_openDecls_4497_);
    crate::leanh::lean_ctor_set(v___x_4507_, 8, v_initHeartbeats_4498_);
    crate::leanh::lean_ctor_set(v___x_4507_, 9, v_maxHeartbeats_4499_);
    crate::leanh::lean_ctor_set(v___x_4507_, 10, v_quotContext_4500_);
    crate::leanh::lean_ctor_set(v___x_4507_, 11, v_currMacroScope_4501_);
    crate::leanh::lean_ctor_set(v___x_4507_, 12, v_cancelTk_x3f_4503_);
    crate::leanh::lean_ctor_set(v___x_4507_, 13, v_inheritedTraceOptions_4505_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4507_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4502_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4507_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4504_,
    );
    v___x_4508_ = l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
        v_msg_4484_,
        v___y_4485_,
        v___y_4486_,
        v___x_4507_,
        v___y_4488_,
    );
    crate::leanh::lean_dec_ref_known(v___x_4507_, 14);
    return v___x_4508_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg___boxed(
    mut v_ref_4509_: *mut crate::leanh::LeanObject,
    mut v_msg_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(
        v_ref_4509_,
        v_msg_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
    );
    crate::leanh::lean_dec(v___y_4514_);
    crate::leanh::lean_dec_ref(v___y_4513_);
    crate::leanh::lean_dec(v___y_4512_);
    crate::leanh::lean_dec_ref(v___y_4511_);
    crate::leanh::lean_dec(v_ref_4509_);
    return v_res_4516_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__0;
    v___x_4519_ = l_Lean_stringToMessageData(v___x_4518_);
    return v___x_4519_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__2;
    v___x_4522_ = l_Lean_stringToMessageData(v___x_4521_);
    return v___x_4522_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__4;
    v___x_4525_ = l_Lean_stringToMessageData(v___x_4524_);
    return v___x_4525_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(
    mut v___x_4526_: u8,
    mut v_projName_4527_: *mut crate::leanh::LeanObject,
    mut v_n_4528_: *mut crate::leanh::LeanObject,
    mut v_ref_4529_: *mut crate::leanh::LeanObject,
    mut v___f_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_4526_ == 0 {
                    v___x_4536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
                    v___x_4537_ = l_Lean_MessageData_ofName(v_projName_4527_);
                    v___x_4538_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4538_, 0, v___x_4536_);
                    crate::leanh::lean_ctor_set(v___x_4538_, 1, v___x_4537_);
                    v___x_4539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
                    v___x_4540_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4540_, 0, v___x_4538_);
                    crate::leanh::lean_ctor_set(v___x_4540_, 1, v___x_4539_);
                    v___x_4541_ = l_Lean_MessageData_ofConstName(v_n_4528_, v___x_4526_);
                    v___x_4542_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4542_, 0, v___x_4540_);
                    crate::leanh::lean_ctor_set(v___x_4542_, 1, v___x_4541_);
                    v___x_4543_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__5);
                    v___x_4544_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4544_, 0, v___x_4542_);
                    crate::leanh::lean_ctor_set(v___x_4544_, 1, v___x_4543_);
                    v___x_4545_ =
                        l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(
                            v_ref_4529_,
                            v___x_4544_,
                            v___y_4531_,
                            v___y_4532_,
                            v___y_4533_,
                            v___y_4534_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4545_) == 0 {
                        v_a_4546_ = crate::leanh::lean_ctor_get(v___x_4545_, 0);
                        crate::leanh::lean_inc(v_a_4546_);
                        crate::leanh::lean_dec_ref_known(v___x_4545_, 1);
                        crate::leanh::lean_inc(v___y_4534_);
                        crate::leanh::lean_inc_ref(v___y_4533_);
                        crate::leanh::lean_inc(v___y_4532_);
                        crate::leanh::lean_inc_ref(v___y_4531_);
                        v___x_4547_ = crate::leanh::lean_apply_6(
                            v___f_4530_,
                            v_a_4546_,
                            v___y_4531_,
                            v___y_4532_,
                            v___y_4533_,
                            v___y_4534_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_4547_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_4530_);
                        v_a_4548_ = crate::leanh::lean_ctor_get(v___x_4545_, 0);
                        v_isSharedCheck_4555_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4545_)) as u8;
                        if v_isSharedCheck_4555_ == 0 {
                            v___x_4550_ = v___x_4545_;
                            v_isShared_4551_ = v_isSharedCheck_4555_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4548_);
                            crate::leanh::lean_dec(v___x_4545_);
                            v___x_4550_ = crate::leanh::lean_box(0);
                            v_isShared_4551_ = v_isSharedCheck_4555_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_n_4528_);
                    crate::leanh::lean_dec(v_projName_4527_);
                    v___x_4556_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_4534_);
                    crate::leanh::lean_inc_ref(v___y_4533_);
                    crate::leanh::lean_inc(v___y_4532_);
                    crate::leanh::lean_inc_ref(v___y_4531_);
                    v___x_4557_ = crate::leanh::lean_apply_6(
                        v___f_4530_,
                        v___x_4556_,
                        v___y_4531_,
                        v___y_4532_,
                        v___y_4533_,
                        v___y_4534_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4557_;
                }
            }
            1 => {
                if v_isShared_4551_ == 0 {
                    v___x_4553_ = v___x_4550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
                    v___x_4553_ = v_reuseFailAlloc_4554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed(
    mut v___x_4558_: *mut crate::leanh::LeanObject,
    mut v_projName_4559_: *mut crate::leanh::LeanObject,
    mut v_n_4560_: *mut crate::leanh::LeanObject,
    mut v_ref_4561_: *mut crate::leanh::LeanObject,
    mut v___f_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_18677__boxed_4568_: u8 = 0;
    let mut v_res_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_18677__boxed_4568_ = (crate::leanh::lean_unbox(v___x_4558_) as u8);
    v_res_4569_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1(
            v___x_18677__boxed_4568_,
            v_projName_4559_,
            v_n_4560_,
            v_ref_4561_,
            v___f_4562_,
            v___y_4563_,
            v___y_4564_,
            v___y_4565_,
            v___y_4566_,
        );
    crate::leanh::lean_dec(v___y_4566_);
    crate::leanh::lean_dec_ref(v___y_4565_);
    crate::leanh::lean_dec(v___y_4564_);
    crate::leanh::lean_dec_ref(v___y_4563_);
    crate::leanh::lean_dec(v_ref_4561_);
    return v_res_4569_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4570_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4571_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__0);
    v___x_4572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4572_, 0, v___x_4571_);
    return v___x_4572_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4573_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
    v___x_4574_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4574_, 0, v___x_4573_);
    crate::leanh::lean_ctor_set(v___x_4574_, 1, v___x_4573_);
    return v___x_4574_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__1);
    v___x_4576_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4576_, 0, v___x_4575_);
    crate::leanh::lean_ctor_set(v___x_4576_, 1, v___x_4575_);
    crate::leanh::lean_ctor_set(v___x_4576_, 2, v___x_4575_);
    crate::leanh::lean_ctor_set(v___x_4576_, 3, v___x_4575_);
    crate::leanh::lean_ctor_set(v___x_4576_, 4, v___x_4575_);
    crate::leanh::lean_ctor_set(v___x_4576_, 5, v___x_4575_);
    return v___x_4576_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(
    mut v_declName_4577_: *mut crate::leanh::LeanObject,
    mut v_s_4578_: u8,
    mut v___y_4579_: *mut crate::leanh::LeanObject,
    mut v___y_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v___x_4594_: u8 = 0;
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4616_: u8 = 0;
    let mut v_unused_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4619_: u8 = 0;
    let mut v_unused_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4582_ = lean_st_ref_take(v___y_4580_);
                v_env_4583_ = crate::leanh::lean_ctor_get(v___x_4582_, 0);
                v_nextMacroScope_4584_ = crate::leanh::lean_ctor_get(v___x_4582_, 1);
                v_ngen_4585_ = crate::leanh::lean_ctor_get(v___x_4582_, 2);
                v_auxDeclNGen_4586_ = crate::leanh::lean_ctor_get(v___x_4582_, 3);
                v_traceState_4587_ = crate::leanh::lean_ctor_get(v___x_4582_, 4);
                v_messages_4588_ = crate::leanh::lean_ctor_get(v___x_4582_, 6);
                v_infoState_4589_ = crate::leanh::lean_ctor_get(v___x_4582_, 7);
                v_snapshotTasks_4590_ = crate::leanh::lean_ctor_get(v___x_4582_, 8);
                v_isSharedCheck_4619_ = (!crate::leanh::lean_is_exclusive(v___x_4582_)) as u8;
                if v_isSharedCheck_4619_ == 0 {
                    v_unused_4620_ = crate::leanh::lean_ctor_get(v___x_4582_, 5);
                    crate::leanh::lean_dec(v_unused_4620_);
                    v___x_4592_ = v___x_4582_;
                    v_isShared_4593_ = v_isSharedCheck_4619_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4590_);
                    crate::leanh::lean_inc(v_infoState_4589_);
                    crate::leanh::lean_inc(v_messages_4588_);
                    crate::leanh::lean_inc(v_traceState_4587_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4586_);
                    crate::leanh::lean_inc(v_ngen_4585_);
                    crate::leanh::lean_inc(v_nextMacroScope_4584_);
                    crate::leanh::lean_inc(v_env_4583_);
                    crate::leanh::lean_dec(v___x_4582_);
                    v___x_4592_ = crate::leanh::lean_box(0);
                    v_isShared_4593_ = v_isSharedCheck_4619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4594_ = 0;
                v___x_4595_ = crate::leanh::lean_box(0);
                v___x_4596_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_4583_,
                    v_declName_4577_,
                    v_s_4578_,
                    v___x_4594_,
                    v___x_4595_,
                );
                v___x_4597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
                if v_isShared_4593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4592_, 5, v___x_4597_);
                    crate::leanh::lean_ctor_set(v___x_4592_, 0, v___x_4596_);
                    v___x_4599_ = v___x_4592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4618_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 1, v_nextMacroScope_4584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 2, v_ngen_4585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 3, v_auxDeclNGen_4586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 4, v_traceState_4587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 5, v___x_4597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 6, v_messages_4588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 7, v_infoState_4589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4618_, 8, v_snapshotTasks_4590_);
                    v___x_4599_ = v_reuseFailAlloc_4618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4600_ = lean_st_ref_set(v___y_4580_, v___x_4599_);
                v___x_4601_ = lean_st_ref_take(v___y_4579_);
                v_mctx_4602_ = crate::leanh::lean_ctor_get(v___x_4601_, 0);
                v_zetaDeltaFVarIds_4603_ = crate::leanh::lean_ctor_get(v___x_4601_, 2);
                v_postponed_4604_ = crate::leanh::lean_ctor_get(v___x_4601_, 3);
                v_diag_4605_ = crate::leanh::lean_ctor_get(v___x_4601_, 4);
                v_isSharedCheck_4616_ = (!crate::leanh::lean_is_exclusive(v___x_4601_)) as u8;
                if v_isSharedCheck_4616_ == 0 {
                    v_unused_4617_ = crate::leanh::lean_ctor_get(v___x_4601_, 1);
                    crate::leanh::lean_dec(v_unused_4617_);
                    v___x_4607_ = v___x_4601_;
                    v_isShared_4608_ = v_isSharedCheck_4616_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4605_);
                    crate::leanh::lean_inc(v_postponed_4604_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4603_);
                    crate::leanh::lean_inc(v_mctx_4602_);
                    crate::leanh::lean_dec(v___x_4601_);
                    v___x_4607_ = crate::leanh::lean_box(0);
                    v_isShared_4608_ = v_isSharedCheck_4616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
                if v_isShared_4608_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4607_, 1, v___x_4609_);
                    v___x_4611_ = v___x_4607_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4615_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_mctx_4602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 1, v___x_4609_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4615_,
                        2,
                        v_zetaDeltaFVarIds_4603_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 3, v_postponed_4604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4615_, 4, v_diag_4605_);
                    v___x_4611_ = v_reuseFailAlloc_4615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4612_ = lean_st_ref_set(v___y_4579_, v___x_4611_);
                v___x_4613_ = crate::leanh::lean_box(0);
                v___x_4614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4614_, 0, v___x_4613_);
                return v___x_4614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___boxed(
    mut v_declName_4621_: *mut crate::leanh::LeanObject,
    mut v_s_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_4626_: u8 = 0;
    let mut v_res_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4626_ = (crate::leanh::lean_unbox(v_s_4622_) as u8);
    v_res_4627_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_4621_, v_s_boxed_4626_, v___y_4623_, v___y_4624_);
    crate::leanh::lean_dec(v___y_4624_);
    crate::leanh::lean_dec(v___y_4623_);
    return v_res_4627_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(
    mut v_declName_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4634_ = 0;
    v___x_4635_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_4628_, v___x_4634_, v___y_4630_, v___y_4632_);
    return v___x_4635_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5___boxed(
    mut v_declName_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4642_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(
        v_declName_4636_,
        v___y_4637_,
        v___y_4638_,
        v___y_4639_,
        v___y_4640_,
    );
    crate::leanh::lean_dec(v___y_4640_);
    crate::leanh::lean_dec_ref(v___y_4639_);
    crate::leanh::lean_dec(v___y_4638_);
    crate::leanh::lean_dec_ref(v___y_4637_);
    return v_res_4642_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__0;
    v___x_4645_ = l_Lean_stringToMessageData(v___x_4644_);
    return v___x_4645_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__2;
    v___x_4648_ = l_Lean_stringToMessageData(v___x_4647_);
    return v___x_4648_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4650_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__4;
    v___x_4651_ = l_Lean_stringToMessageData(v___x_4650_);
    return v___x_4651_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(
    mut v___x_4652_: *mut crate::leanh::LeanObject,
    mut v_projName_4653_: *mut crate::leanh::LeanObject,
    mut v___x_4654_: *mut crate::leanh::LeanObject,
    mut v_a_4655_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_4656_: u8,
    mut v___x_4657_: *mut crate::leanh::LeanObject,
    mut v_params_4658_: *mut crate::leanh::LeanObject,
    mut v_self_4659_: *mut crate::leanh::LeanObject,
    mut v_b_4660_: *mut crate::leanh::LeanObject,
    mut v___x_4661_: u8,
    mut v_a_4662_: *mut crate::leanh::LeanObject,
    mut v___x_4663_: *mut crate::leanh::LeanObject,
    mut v_paramInfoOverrides_4664_: *mut crate::leanh::LeanObject,
    mut v_n_4665_: *mut crate::leanh::LeanObject,
    mut v_ref_4666_: *mut crate::leanh::LeanObject,
    mut v___x_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: u8,
    mut v_____r_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v_name_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4703_: u8 = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_unused_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4718_: u8 = 0;
    let mut v_unused_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut v___y_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4736_: u8 = 0;
    let mut v___y_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4746_: u8 = 0;
    let mut v___y_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4765_: u8 = 0;
    let mut v_cancelTk_x3f_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4767_: u8 = 0;
    let mut v_inheritedTraceOptions_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: u8 = 0;
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: u8 = 0;
    let mut v_a_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v_a_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4824_: u8 = 0;
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4828_: u8 = 0;
    let mut v___x_4829_: u8 = 0;
    let mut v_a_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4833_: u8 = 0;
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4837_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: u8 = 0;
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4854_: u8 = 0;
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4838_ = l_List_lengthTR___redArg(v_paramInfoOverrides_4664_);
                v___x_4839_ = lean_array_get_size(v_params_4658_);
                v___x_4840_ = lean_nat_dec_le(v___x_4838_, v___x_4839_);
                crate::leanh::lean_dec(v___x_4838_);
                if v___x_4840_ == 0 {
                    v___x_4841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
                    crate::leanh::lean_inc(v_projName_4653_);
                    v___x_4842_ = l_Lean_MessageData_ofName(v_projName_4653_);
                    v___x_4843_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4843_, 0, v___x_4841_);
                    crate::leanh::lean_ctor_set(v___x_4843_, 1, v___x_4842_);
                    v___x_4844_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__3);
                    v___x_4845_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4845_, 0, v___x_4843_);
                    crate::leanh::lean_ctor_set(v___x_4845_, 1, v___x_4844_);
                    crate::leanh::lean_inc(v_n_4665_);
                    v___x_4846_ = l_Lean_MessageData_ofConstName(v_n_4665_, v___x_4840_);
                    v___x_4847_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4847_, 0, v___x_4845_);
                    crate::leanh::lean_ctor_set(v___x_4847_, 1, v___x_4846_);
                    v___x_4848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__5);
                    v___x_4849_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4849_, 0, v___x_4847_);
                    crate::leanh::lean_ctor_set(v___x_4849_, 1, v___x_4848_);
                    v___x_4850_ =
                        l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(
                            v_ref_4666_,
                            v___x_4849_,
                            v___y_4670_,
                            v___y_4671_,
                            v___y_4672_,
                            v___y_4673_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4850_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4850_, 1);
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4667_);
                        crate::leanh::lean_dec(v_n_4665_);
                        crate::leanh::lean_dec_ref(v_a_4662_);
                        crate::leanh::lean_dec_ref(v_self_4659_);
                        crate::leanh::lean_dec(v___x_4657_);
                        crate::leanh::lean_dec(v_a_4655_);
                        crate::leanh::lean_dec(v___x_4654_);
                        crate::leanh::lean_dec(v_projName_4653_);
                        crate::leanh::lean_dec_ref(v___x_4652_);
                        v_a_4851_ = crate::leanh::lean_ctor_get(v___x_4850_, 0);
                        v_isSharedCheck_4858_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4850_)) as u8;
                        if v_isSharedCheck_4858_ == 0 {
                            v___x_4853_ = v___x_4850_;
                            v_isShared_4854_ = v_isSharedCheck_4858_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4851_);
                            crate::leanh::lean_dec(v___x_4850_);
                            v___x_4853_ = crate::leanh::lean_box(0);
                            v_isShared_4854_ = v_isSharedCheck_4858_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    state = 13;
                    continue;
                }
            }
            1 => {
                v___x_4678_ = lean_st_ref_take(v___y_4677_);
                v_env_4679_ = crate::leanh::lean_ctor_get(v___x_4678_, 0);
                v_nextMacroScope_4680_ = crate::leanh::lean_ctor_get(v___x_4678_, 1);
                v_ngen_4681_ = crate::leanh::lean_ctor_get(v___x_4678_, 2);
                v_auxDeclNGen_4682_ = crate::leanh::lean_ctor_get(v___x_4678_, 3);
                v_traceState_4683_ = crate::leanh::lean_ctor_get(v___x_4678_, 4);
                v_messages_4684_ = crate::leanh::lean_ctor_get(v___x_4678_, 6);
                v_infoState_4685_ = crate::leanh::lean_ctor_get(v___x_4678_, 7);
                v_snapshotTasks_4686_ = crate::leanh::lean_ctor_get(v___x_4678_, 8);
                v_isSharedCheck_4718_ = (!crate::leanh::lean_is_exclusive(v___x_4678_)) as u8;
                if v_isSharedCheck_4718_ == 0 {
                    v_unused_4719_ = crate::leanh::lean_ctor_get(v___x_4678_, 5);
                    crate::leanh::lean_dec(v_unused_4719_);
                    v___x_4688_ = v___x_4678_;
                    v_isShared_4689_ = v_isSharedCheck_4718_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4686_);
                    crate::leanh::lean_inc(v_infoState_4685_);
                    crate::leanh::lean_inc(v_messages_4684_);
                    crate::leanh::lean_inc(v_traceState_4683_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4682_);
                    crate::leanh::lean_inc(v_ngen_4681_);
                    crate::leanh::lean_inc(v_nextMacroScope_4680_);
                    crate::leanh::lean_inc(v_env_4679_);
                    crate::leanh::lean_dec(v___x_4678_);
                    v___x_4688_ = crate::leanh::lean_box(0);
                    v_isShared_4689_ = v_isSharedCheck_4718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_name_4690_ = crate::leanh::lean_ctor_get(v___x_4652_, 0);
                crate::leanh::lean_inc(v_name_4690_);
                crate::leanh::lean_dec_ref(v___x_4652_);
                crate::leanh::lean_inc(v_projName_4653_);
                v___x_4691_ = l_Lean_addProjectionFnInfo(
                    v_env_4679_,
                    v_projName_4653_,
                    v_name_4690_,
                    v___x_4654_,
                    v_a_4655_,
                    v_instImplicit_4656_,
                );
                v___x_4692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
                if v_isShared_4689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4688_, 5, v___x_4692_);
                    crate::leanh::lean_ctor_set(v___x_4688_, 0, v___x_4691_);
                    v___x_4694_ = v___x_4688_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4717_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 0, v___x_4691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 1, v_nextMacroScope_4680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 2, v_ngen_4681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 3, v_auxDeclNGen_4682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 4, v_traceState_4683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 5, v___x_4692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 6, v_messages_4684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 7, v_infoState_4685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4717_, 8, v_snapshotTasks_4686_);
                    v___x_4694_ = v_reuseFailAlloc_4717_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4695_ = lean_st_ref_set(v___y_4677_, v___x_4694_);
                v___x_4696_ = lean_st_ref_take(v___y_4676_);
                v_mctx_4697_ = crate::leanh::lean_ctor_get(v___x_4696_, 0);
                v_zetaDeltaFVarIds_4698_ = crate::leanh::lean_ctor_get(v___x_4696_, 2);
                v_postponed_4699_ = crate::leanh::lean_ctor_get(v___x_4696_, 3);
                v_diag_4700_ = crate::leanh::lean_ctor_get(v___x_4696_, 4);
                v_isSharedCheck_4715_ = (!crate::leanh::lean_is_exclusive(v___x_4696_)) as u8;
                if v_isSharedCheck_4715_ == 0 {
                    v_unused_4716_ = crate::leanh::lean_ctor_get(v___x_4696_, 1);
                    crate::leanh::lean_dec(v_unused_4716_);
                    v___x_4702_ = v___x_4696_;
                    v_isShared_4703_ = v_isSharedCheck_4715_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4700_);
                    crate::leanh::lean_inc(v_postponed_4699_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4698_);
                    crate::leanh::lean_inc(v_mctx_4697_);
                    crate::leanh::lean_dec(v___x_4696_);
                    v___x_4702_ = crate::leanh::lean_box(0);
                    v_isShared_4703_ = v_isSharedCheck_4715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4704_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
                if v_isShared_4703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4702_, 1, v___x_4704_);
                    v___x_4706_ = v___x_4702_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4714_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_mctx_4697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4704_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4714_,
                        2,
                        v_zetaDeltaFVarIds_4698_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 3, v_postponed_4699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 4, v_diag_4700_);
                    v___x_4706_ = v_reuseFailAlloc_4714_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4707_ = lean_st_ref_set(v___y_4676_, v___x_4706_);
                v___x_4708_ = l_Lean_Expr_const___override(v_projName_4653_, v___x_4657_);
                v___x_4709_ = l_Lean_mkAppN(v___x_4708_, v_params_4658_);
                v___x_4710_ = l_Lean_Expr_app___override(v___x_4709_, v_self_4659_);
                v___x_4711_ = l_Lean_Expr_bindingBody_x21(v_b_4660_);
                v___x_4712_ = lean_expr_instantiate1(v___x_4711_, v___x_4710_);
                crate::leanh::lean_dec_ref(v___x_4710_);
                crate::leanh::lean_dec_ref(v___x_4711_);
                v___x_4713_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4713_, 0, v___x_4712_);
                return v___x_4713_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_4723_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4723_, 1);
                    v___y_4676_ = v___y_4721_;
                    v___y_4677_ = v___y_4722_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_self_4659_);
                    crate::leanh::lean_dec(v___x_4657_);
                    crate::leanh::lean_dec(v_a_4655_);
                    crate::leanh::lean_dec(v___x_4654_);
                    crate::leanh::lean_dec(v_projName_4653_);
                    crate::leanh::lean_dec_ref(v___x_4652_);
                    v_a_4724_ = crate::leanh::lean_ctor_get(v___y_4723_, 0);
                    v_isSharedCheck_4731_ = (!crate::leanh::lean_is_exclusive(v___y_4723_)) as u8;
                    if v_isSharedCheck_4731_ == 0 {
                        v___x_4726_ = v___y_4723_;
                        v_isShared_4727_ = v_isSharedCheck_4731_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4724_);
                        crate::leanh::lean_dec(v___y_4723_);
                        v___x_4726_ = crate::leanh::lean_box(0);
                        v_isShared_4727_ = v_isSharedCheck_4731_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4727_ == 0 {
                    v___x_4729_ = v___x_4726_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
                    v___x_4729_ = v_reuseFailAlloc_4730_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4729_;
            }
            9 => {
                v___x_4739_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_projName_4653_);
                v___x_4740_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4740_, 0, v_projName_4653_);
                crate::leanh::lean_ctor_set(v___x_4740_, 1, v___x_4739_);
                v___x_4741_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4741_, 0, v___y_4738_);
                crate::leanh::lean_ctor_set(v___x_4741_, 1, v___y_4734_);
                crate::leanh::lean_ctor_set(v___x_4741_, 2, v___x_4740_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4741_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4661_,
                );
                v___x_4742_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4742_, 0, v___x_4741_);
                v___x_4743_ = l_Lean_addDecl(v___x_4742_, v___y_4736_, v___y_4735_, v___y_4737_);
                crate::leanh::lean_dec_ref(v___y_4735_);
                v___y_4721_ = v___y_4733_;
                v___y_4722_ = v___y_4737_;
                v___y_4723_ = v___x_4743_;
                state = 6;
                continue;
            }
            10 => {
                v___x_4751_ = 0;
                crate::leanh::lean_inc_ref(v_a_4662_);
                v___x_4752_ = l_Lean_LocalContext_mkForall(
                    v_a_4662_,
                    v___x_4663_,
                    v___y_4745_,
                    v___x_4661_,
                    v___x_4751_,
                );
                crate::leanh::lean_dec_ref(v___y_4745_);
                v_fileName_4753_ = crate::leanh::lean_ctor_get(v___y_4749_, 0);
                v_fileMap_4754_ = crate::leanh::lean_ctor_get(v___y_4749_, 1);
                v_options_4755_ = crate::leanh::lean_ctor_get(v___y_4749_, 2);
                v_currRecDepth_4756_ = crate::leanh::lean_ctor_get(v___y_4749_, 3);
                v_maxRecDepth_4757_ = crate::leanh::lean_ctor_get(v___y_4749_, 4);
                v_ref_4758_ = crate::leanh::lean_ctor_get(v___y_4749_, 5);
                v_currNamespace_4759_ = crate::leanh::lean_ctor_get(v___y_4749_, 6);
                v_openDecls_4760_ = crate::leanh::lean_ctor_get(v___y_4749_, 7);
                v_initHeartbeats_4761_ = crate::leanh::lean_ctor_get(v___y_4749_, 8);
                v_maxHeartbeats_4762_ = crate::leanh::lean_ctor_get(v___y_4749_, 9);
                v_quotContext_4763_ = crate::leanh::lean_ctor_get(v___y_4749_, 10);
                v_currMacroScope_4764_ = crate::leanh::lean_ctor_get(v___y_4749_, 11);
                v_diag_4765_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4749_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4766_ = crate::leanh::lean_ctor_get(v___y_4749_, 12);
                v_suppressElabErrors_4767_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4749_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4768_ = crate::leanh::lean_ctor_get(v___y_4749_, 13);
                v___x_4769_ = l_Lean_Expr_inferImplicit(v___x_4752_, v___x_4654_, v___x_4661_);
                v___x_4770_ =
                    l_Lean_Expr_updateForallBinderInfos(v___x_4769_, v_paramInfoOverrides_4664_);
                crate::leanh::lean_inc_ref(v_self_4659_);
                crate::leanh::lean_inc(v_a_4655_);
                v___x_4771_ = l_Lean_Expr_proj___override(v_n_4665_, v_a_4655_, v_self_4659_);
                v___x_4772_ = l_Lean_LocalContext_mkLambda(
                    v_a_4662_,
                    v___x_4663_,
                    v___x_4771_,
                    v___x_4661_,
                    v___x_4751_,
                );
                crate::leanh::lean_dec_ref(v___x_4771_);
                v_ref_4773_ = l_Lean_replaceRef(v_ref_4666_, v_ref_4758_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4768_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4766_);
                crate::leanh::lean_inc(v_currMacroScope_4764_);
                crate::leanh::lean_inc(v_quotContext_4763_);
                crate::leanh::lean_inc(v_maxHeartbeats_4762_);
                crate::leanh::lean_inc(v_initHeartbeats_4761_);
                crate::leanh::lean_inc(v_openDecls_4760_);
                crate::leanh::lean_inc(v_currNamespace_4759_);
                crate::leanh::lean_inc(v_maxRecDepth_4757_);
                crate::leanh::lean_inc(v_currRecDepth_4756_);
                crate::leanh::lean_inc_ref(v_options_4755_);
                crate::leanh::lean_inc_ref(v_fileMap_4754_);
                crate::leanh::lean_inc_ref(v_fileName_4753_);
                v___x_4774_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4774_, 0, v_fileName_4753_);
                crate::leanh::lean_ctor_set(v___x_4774_, 1, v_fileMap_4754_);
                crate::leanh::lean_ctor_set(v___x_4774_, 2, v_options_4755_);
                crate::leanh::lean_ctor_set(v___x_4774_, 3, v_currRecDepth_4756_);
                crate::leanh::lean_ctor_set(v___x_4774_, 4, v_maxRecDepth_4757_);
                crate::leanh::lean_ctor_set(v___x_4774_, 5, v_ref_4773_);
                crate::leanh::lean_ctor_set(v___x_4774_, 6, v_currNamespace_4759_);
                crate::leanh::lean_ctor_set(v___x_4774_, 7, v_openDecls_4760_);
                crate::leanh::lean_ctor_set(v___x_4774_, 8, v_initHeartbeats_4761_);
                crate::leanh::lean_ctor_set(v___x_4774_, 9, v_maxHeartbeats_4762_);
                crate::leanh::lean_ctor_set(v___x_4774_, 10, v_quotContext_4763_);
                crate::leanh::lean_ctor_set(v___x_4774_, 11, v_currMacroScope_4764_);
                crate::leanh::lean_ctor_set(v___x_4774_, 12, v_cancelTk_x3f_4766_);
                crate::leanh::lean_ctor_set(v___x_4774_, 13, v_inheritedTraceOptions_4768_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4774_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4765_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4774_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4767_,
                );
                if v___y_4746_ == 0 {
                    v___x_4775_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v_projName_4653_);
                    v___x_4776_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkProjections_spec__4___redArg(v_projName_4653_, v___x_4667_, v___x_4770_, v___x_4772_, v___x_4775_, v___y_4750_);
                    if crate::leanh::lean_obj_tag(v___x_4776_) == 0 {
                        v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                        crate::leanh::lean_inc(v_a_4777_);
                        crate::leanh::lean_dec_ref_known(v___x_4776_, 1);
                        v___x_4778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4778_, 0, v_a_4777_);
                        v___x_4779_ =
                            l_Lean_addDecl(v___x_4778_, v___x_4751_, v___x_4774_, v___y_4750_);
                        if crate::leanh::lean_obj_tag(v___x_4779_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4779_, 1);
                            if v_instImplicit_4656_ == 0 {
                                crate::leanh::lean_inc(v_projName_4653_);
                                v___x_4780_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5(v_projName_4653_, v___y_4747_, v___y_4748_, v___x_4774_, v___y_4750_);
                                crate::leanh::lean_dec_ref_known(v___x_4774_, 14);
                                v___y_4721_ = v___y_4748_;
                                v___y_4722_ = v___y_4750_;
                                v___y_4723_ = v___x_4780_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_4774_, 14);
                                v___y_4676_ = v___y_4748_;
                                v___y_4677_ = v___y_4750_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4774_, 14);
                            v___y_4721_ = v___y_4748_;
                            v___y_4722_ = v___y_4750_;
                            v___y_4723_ = v___x_4779_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4774_, 14);
                        crate::leanh::lean_dec_ref(v_self_4659_);
                        crate::leanh::lean_dec(v___x_4657_);
                        crate::leanh::lean_dec(v_a_4655_);
                        crate::leanh::lean_dec(v___x_4654_);
                        crate::leanh::lean_dec(v_projName_4653_);
                        crate::leanh::lean_dec_ref(v___x_4652_);
                        v_a_4781_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                        v_isSharedCheck_4788_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4776_)) as u8;
                        if v_isSharedCheck_4788_ == 0 {
                            v___x_4783_ = v___x_4776_;
                            v_isShared_4784_ = v_isSharedCheck_4788_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4781_);
                            crate::leanh::lean_dec(v___x_4776_);
                            v___x_4783_ = crate::leanh::lean_box(0);
                            v_isShared_4784_ = v_isSharedCheck_4788_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v___x_4789_ = lean_st_ref_get(v___y_4750_);
                    v_env_4790_ = crate::leanh::lean_ctor_get(v___x_4789_, 0);
                    crate::leanh::lean_inc_ref_n(v_env_4790_, 2);
                    crate::leanh::lean_dec(v___x_4789_);
                    crate::leanh::lean_inc_ref(v___x_4770_);
                    crate::leanh::lean_inc(v_projName_4653_);
                    v___x_4791_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4791_, 0, v_projName_4653_);
                    crate::leanh::lean_ctor_set(v___x_4791_, 1, v___x_4667_);
                    crate::leanh::lean_ctor_set(v___x_4791_, 2, v___x_4770_);
                    v___x_4792_ = l_Lean_Environment_hasUnsafe(v_env_4790_, v___x_4770_);
                    crate::leanh::lean_dec_ref(v___x_4770_);
                    if v___x_4792_ == 0 {
                        v___x_4793_ = l_Lean_Environment_hasUnsafe(v_env_4790_, v___x_4772_);
                        if v___x_4793_ == 0 {
                            v___x_4794_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_projName_4653_);
                            v___x_4795_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4795_, 0, v_projName_4653_);
                            crate::leanh::lean_ctor_set(v___x_4795_, 1, v___x_4794_);
                            v___x_4796_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4796_, 0, v___x_4791_);
                            crate::leanh::lean_ctor_set(v___x_4796_, 1, v___x_4772_);
                            crate::leanh::lean_ctor_set(v___x_4796_, 2, v___x_4795_);
                            v___x_4797_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4797_, 0, v___x_4796_);
                            v___x_4798_ =
                                l_Lean_addDecl(v___x_4797_, v___x_4751_, v___x_4774_, v___y_4750_);
                            crate::leanh::lean_dec_ref_known(v___x_4774_, 14);
                            v___y_4721_ = v___y_4748_;
                            v___y_4722_ = v___y_4750_;
                            v___y_4723_ = v___x_4798_;
                            state = 6;
                            continue;
                        } else {
                            v___y_4733_ = v___y_4748_;
                            v___y_4734_ = v___x_4772_;
                            v___y_4735_ = v___x_4774_;
                            v___y_4736_ = v___x_4751_;
                            v___y_4737_ = v___y_4750_;
                            v___y_4738_ = v___x_4791_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_env_4790_);
                        v___y_4733_ = v___y_4748_;
                        v___y_4734_ = v___x_4772_;
                        v___y_4735_ = v___x_4774_;
                        v___y_4736_ = v___x_4751_;
                        v___y_4737_ = v___y_4750_;
                        v___y_4738_ = v___x_4791_;
                        state = 9;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4784_ == 0 {
                    v___x_4786_ = v___x_4783_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
                    v___x_4786_ = v_reuseFailAlloc_4787_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4786_;
            }
            13 => {
                v___x_4800_ = l_Lean_Expr_bindingDomain_x21(v_b_4660_);
                v___x_4801_ = lean_expr_consume_type_annotations(v___x_4800_);
                crate::leanh::lean_inc_ref(v___x_4801_);
                v___x_4802_ = l_Lean_Meta_isProp(
                    v___x_4801_,
                    v___y_4670_,
                    v___y_4671_,
                    v___y_4672_,
                    v___y_4673_,
                );
                if crate::leanh::lean_obj_tag(v___x_4802_) == 0 {
                    if v_a_4668_ == 0 {
                        v_a_4803_ = crate::leanh::lean_ctor_get(v___x_4802_, 0);
                        crate::leanh::lean_inc(v_a_4803_);
                        crate::leanh::lean_dec_ref_known(v___x_4802_, 1);
                        v___x_4804_ = (crate::leanh::lean_unbox(v_a_4803_) as u8);
                        crate::leanh::lean_dec(v_a_4803_);
                        v___y_4745_ = v___x_4801_;
                        v___y_4746_ = v___x_4804_;
                        v___y_4747_ = v___y_4670_;
                        v___y_4748_ = v___y_4671_;
                        v___y_4749_ = v___y_4672_;
                        v___y_4750_ = v___y_4673_;
                        state = 10;
                        continue;
                    } else {
                        v_a_4805_ = crate::leanh::lean_ctor_get(v___x_4802_, 0);
                        crate::leanh::lean_inc(v_a_4805_);
                        crate::leanh::lean_dec_ref_known(v___x_4802_, 1);
                        v___x_4806_ = (crate::leanh::lean_unbox(v_a_4805_) as u8);
                        if v___x_4806_ == 0 {
                            v___x_4807_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___closed__1);
                            crate::leanh::lean_inc(v_projName_4653_);
                            v___x_4808_ = l_Lean_MessageData_ofName(v_projName_4653_);
                            v___x_4809_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4809_, 0, v___x_4807_);
                            crate::leanh::lean_ctor_set(v___x_4809_, 1, v___x_4808_);
                            v___x_4810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__1);
                            v___x_4811_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4811_, 0, v___x_4809_);
                            crate::leanh::lean_ctor_set(v___x_4811_, 1, v___x_4810_);
                            v___x_4812_ = (crate::leanh::lean_unbox(v_a_4805_) as u8);
                            crate::leanh::lean_inc(v_n_4665_);
                            v___x_4813_ = l_Lean_MessageData_ofConstName(v_n_4665_, v___x_4812_);
                            v___x_4814_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4814_, 0, v___x_4811_);
                            crate::leanh::lean_ctor_set(v___x_4814_, 1, v___x_4813_);
                            v___x_4815_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___closed__3);
                            v___x_4816_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4816_, 0, v___x_4814_);
                            crate::leanh::lean_ctor_set(v___x_4816_, 1, v___x_4815_);
                            crate::leanh::lean_inc_ref(v___x_4801_);
                            v___x_4817_ = l_Lean_indentExpr(v___x_4801_);
                            v___x_4818_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4818_, 0, v___x_4816_);
                            crate::leanh::lean_ctor_set(v___x_4818_, 1, v___x_4817_);
                            v___x_4819_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(v_ref_4666_, v___x_4818_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
                            if crate::leanh::lean_obj_tag(v___x_4819_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4819_, 1);
                                v___x_4820_ = (crate::leanh::lean_unbox(v_a_4805_) as u8);
                                crate::leanh::lean_dec(v_a_4805_);
                                v___y_4745_ = v___x_4801_;
                                v___y_4746_ = v___x_4820_;
                                v___y_4747_ = v___y_4670_;
                                v___y_4748_ = v___y_4671_;
                                v___y_4749_ = v___y_4672_;
                                v___y_4750_ = v___y_4673_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_4805_);
                                crate::leanh::lean_dec_ref(v___x_4801_);
                                crate::leanh::lean_dec(v___x_4667_);
                                crate::leanh::lean_dec(v_n_4665_);
                                crate::leanh::lean_dec_ref(v_a_4662_);
                                crate::leanh::lean_dec_ref(v_self_4659_);
                                crate::leanh::lean_dec(v___x_4657_);
                                crate::leanh::lean_dec(v_a_4655_);
                                crate::leanh::lean_dec(v___x_4654_);
                                crate::leanh::lean_dec(v_projName_4653_);
                                crate::leanh::lean_dec_ref(v___x_4652_);
                                v_a_4821_ = crate::leanh::lean_ctor_get(v___x_4819_, 0);
                                v_isSharedCheck_4828_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4819_)) as u8;
                                if v_isSharedCheck_4828_ == 0 {
                                    v___x_4823_ = v___x_4819_;
                                    v_isShared_4824_ = v_isSharedCheck_4828_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4821_);
                                    crate::leanh::lean_dec(v___x_4819_);
                                    v___x_4823_ = crate::leanh::lean_box(0);
                                    v_isShared_4824_ = v_isSharedCheck_4828_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4829_ = (crate::leanh::lean_unbox(v_a_4805_) as u8);
                            crate::leanh::lean_dec(v_a_4805_);
                            v___y_4745_ = v___x_4801_;
                            v___y_4746_ = v___x_4829_;
                            v___y_4747_ = v___y_4670_;
                            v___y_4748_ = v___y_4671_;
                            v___y_4749_ = v___y_4672_;
                            v___y_4750_ = v___y_4673_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4801_);
                    crate::leanh::lean_dec(v___x_4667_);
                    crate::leanh::lean_dec(v_n_4665_);
                    crate::leanh::lean_dec_ref(v_a_4662_);
                    crate::leanh::lean_dec_ref(v_self_4659_);
                    crate::leanh::lean_dec(v___x_4657_);
                    crate::leanh::lean_dec(v_a_4655_);
                    crate::leanh::lean_dec(v___x_4654_);
                    crate::leanh::lean_dec(v_projName_4653_);
                    crate::leanh::lean_dec_ref(v___x_4652_);
                    v_a_4830_ = crate::leanh::lean_ctor_get(v___x_4802_, 0);
                    v_isSharedCheck_4837_ = (!crate::leanh::lean_is_exclusive(v___x_4802_)) as u8;
                    if v_isSharedCheck_4837_ == 0 {
                        v___x_4832_ = v___x_4802_;
                        v_isShared_4833_ = v_isSharedCheck_4837_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4830_);
                        crate::leanh::lean_dec(v___x_4802_);
                        v___x_4832_ = crate::leanh::lean_box(0);
                        v_isShared_4833_ = v_isSharedCheck_4837_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4824_ == 0 {
                    v___x_4826_ = v___x_4823_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
                    v___x_4826_ = v_reuseFailAlloc_4827_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4826_;
            }
            16 => {
                if v_isShared_4833_ == 0 {
                    v___x_4835_ = v___x_4832_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
                    v___x_4835_ = v_reuseFailAlloc_4836_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4835_;
            }
            18 => {
                if v_isShared_4854_ == 0 {
                    v___x_4856_ = v___x_4853_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
                    v___x_4856_ = v_reuseFailAlloc_4857_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4859_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_projName_4860_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4861_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_4862_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_instImplicit_4863_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4864_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_params_4865_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_self_4866_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_4867_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_4868_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4869_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_4870_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_paramInfoOverrides_4871_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_n_4872_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_ref_4873_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_4874_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4875_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_____r_4876_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4877_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_4878_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_4879_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_4880_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_4881_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_instImplicit_boxed_4882_: u8 = 0;
    let mut v___x_18916__boxed_4883_: u8 = 0;
    let mut v_a_18922__boxed_4884_: u8 = 0;
    let mut v_res_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_4882_ = (crate::leanh::lean_unbox(v_instImplicit_4863_) as u8);
    v___x_18916__boxed_4883_ = (crate::leanh::lean_unbox(v___x_4868_) as u8);
    v_a_18922__boxed_4884_ = (crate::leanh::lean_unbox(v_a_4875_) as u8);
    v_res_4885_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0(
            v___x_4859_,
            v_projName_4860_,
            v___x_4861_,
            v_a_4862_,
            v_instImplicit_boxed_4882_,
            v___x_4864_,
            v_params_4865_,
            v_self_4866_,
            v_b_4867_,
            v___x_18916__boxed_4883_,
            v_a_4869_,
            v___x_4870_,
            v_paramInfoOverrides_4871_,
            v_n_4872_,
            v_ref_4873_,
            v___x_4874_,
            v_a_18922__boxed_4884_,
            v_____r_4876_,
            v___y_4877_,
            v___y_4878_,
            v___y_4879_,
            v___y_4880_,
        );
    crate::leanh::lean_dec(v___y_4880_);
    crate::leanh::lean_dec_ref(v___y_4879_);
    crate::leanh::lean_dec(v___y_4878_);
    crate::leanh::lean_dec_ref(v___y_4877_);
    crate::leanh::lean_dec(v_ref_4873_);
    crate::leanh::lean_dec(v_paramInfoOverrides_4871_);
    crate::leanh::lean_dec_ref(v___x_4870_);
    crate::leanh::lean_dec_ref(v_b_4867_);
    crate::leanh::lean_dec_ref(v_params_4865_);
    return v_res_4885_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4887_: u8,
    mut v___x_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___x_4890_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_unused_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4926_: u8 = 0;
    let mut v_unused_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4893_ = lean_st_ref_take(v___y_4886_);
                v_env_4894_ = crate::leanh::lean_ctor_get(v___x_4893_, 0);
                v_nextMacroScope_4895_ = crate::leanh::lean_ctor_get(v___x_4893_, 1);
                v_ngen_4896_ = crate::leanh::lean_ctor_get(v___x_4893_, 2);
                v_auxDeclNGen_4897_ = crate::leanh::lean_ctor_get(v___x_4893_, 3);
                v_traceState_4898_ = crate::leanh::lean_ctor_get(v___x_4893_, 4);
                v_messages_4899_ = crate::leanh::lean_ctor_get(v___x_4893_, 6);
                v_infoState_4900_ = crate::leanh::lean_ctor_get(v___x_4893_, 7);
                v_snapshotTasks_4901_ = crate::leanh::lean_ctor_get(v___x_4893_, 8);
                v_isSharedCheck_4926_ = (!crate::leanh::lean_is_exclusive(v___x_4893_)) as u8;
                if v_isSharedCheck_4926_ == 0 {
                    v_unused_4927_ = crate::leanh::lean_ctor_get(v___x_4893_, 5);
                    crate::leanh::lean_dec(v_unused_4927_);
                    v___x_4903_ = v___x_4893_;
                    v_isShared_4904_ = v_isSharedCheck_4926_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4901_);
                    crate::leanh::lean_inc(v_infoState_4900_);
                    crate::leanh::lean_inc(v_messages_4899_);
                    crate::leanh::lean_inc(v_traceState_4898_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4897_);
                    crate::leanh::lean_inc(v_ngen_4896_);
                    crate::leanh::lean_inc(v_nextMacroScope_4895_);
                    crate::leanh::lean_inc(v_env_4894_);
                    crate::leanh::lean_dec(v___x_4893_);
                    v___x_4903_ = crate::leanh::lean_box(0);
                    v_isShared_4904_ = v_isSharedCheck_4926_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4905_ = l_Lean_Environment_setExporting(v_env_4894_, v_isExporting_4887_);
                if v_isShared_4904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4903_, 5, v___x_4888_);
                    crate::leanh::lean_ctor_set(v___x_4903_, 0, v___x_4905_);
                    v___x_4907_ = v___x_4903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4925_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 0, v___x_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 1, v_nextMacroScope_4895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 2, v_ngen_4896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 3, v_auxDeclNGen_4897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 4, v_traceState_4898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 5, v___x_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 6, v_messages_4899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 7, v_infoState_4900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4925_, 8, v_snapshotTasks_4901_);
                    v___x_4907_ = v_reuseFailAlloc_4925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4908_ = lean_st_ref_set(v___y_4886_, v___x_4907_);
                v___x_4909_ = lean_st_ref_take(v___y_4889_);
                v_mctx_4910_ = crate::leanh::lean_ctor_get(v___x_4909_, 0);
                v_zetaDeltaFVarIds_4911_ = crate::leanh::lean_ctor_get(v___x_4909_, 2);
                v_postponed_4912_ = crate::leanh::lean_ctor_get(v___x_4909_, 3);
                v_diag_4913_ = crate::leanh::lean_ctor_get(v___x_4909_, 4);
                v_isSharedCheck_4923_ = (!crate::leanh::lean_is_exclusive(v___x_4909_)) as u8;
                if v_isSharedCheck_4923_ == 0 {
                    v_unused_4924_ = crate::leanh::lean_ctor_get(v___x_4909_, 1);
                    crate::leanh::lean_dec(v_unused_4924_);
                    v___x_4915_ = v___x_4909_;
                    v_isShared_4916_ = v_isSharedCheck_4923_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4913_);
                    crate::leanh::lean_inc(v_postponed_4912_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4911_);
                    crate::leanh::lean_inc(v_mctx_4910_);
                    crate::leanh::lean_dec(v___x_4909_);
                    v___x_4915_ = crate::leanh::lean_box(0);
                    v_isShared_4916_ = v_isSharedCheck_4923_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4915_, 1, v___x_4890_);
                    v___x_4918_ = v___x_4915_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_mctx_4910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 1, v___x_4890_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4922_,
                        2,
                        v_zetaDeltaFVarIds_4911_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 3, v_postponed_4912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 4, v_diag_4913_);
                    v___x_4918_ = v_reuseFailAlloc_4922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4919_ = lean_st_ref_set(v___y_4889_, v___x_4918_);
                v___x_4920_ = crate::leanh::lean_box(0);
                v___x_4921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4921_, 0, v___x_4920_);
                return v___x_4921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0___boxed(
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4929_: *mut crate::leanh::LeanObject,
    mut v___x_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___x_4932_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4935_: u8 = 0;
    let mut v_res_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4935_ = (crate::leanh::lean_unbox(v_isExporting_4929_) as u8);
    v_res_4936_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_4928_, v_isExporting_boxed_4935_, v___x_4930_, v___y_4931_, v___x_4932_, v_a_x3f_4933_);
    crate::leanh::lean_dec(v_a_x3f_4933_);
    crate::leanh::lean_dec(v___y_4931_);
    crate::leanh::lean_dec(v___y_4928_);
    return v_res_4936_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(
    mut v_x_4937_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4938_: u8,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4946_: u8 = 0;
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4958_: u8 = 0;
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4971_: u8 = 0;
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4986_: u8 = 0;
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v_unused_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4993_: u8 = 0;
    let mut v_a_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4999_: u8 = 0;
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5003_: u8 = 0;
    let mut v_unused_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut v_unused_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5009_: u8 = 0;
    let mut v_unused_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4944_ = lean_st_ref_get(v___y_4942_);
                v_env_4945_ = crate::leanh::lean_ctor_get(v___x_4944_, 0);
                crate::leanh::lean_inc_ref(v_env_4945_);
                crate::leanh::lean_dec(v___x_4944_);
                v_isExporting_4946_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4945_);
                v___x_4947_ = lean_st_ref_take(v___y_4942_);
                v_env_4948_ = crate::leanh::lean_ctor_get(v___x_4947_, 0);
                v_nextMacroScope_4949_ = crate::leanh::lean_ctor_get(v___x_4947_, 1);
                v_ngen_4950_ = crate::leanh::lean_ctor_get(v___x_4947_, 2);
                v_auxDeclNGen_4951_ = crate::leanh::lean_ctor_get(v___x_4947_, 3);
                v_traceState_4952_ = crate::leanh::lean_ctor_get(v___x_4947_, 4);
                v_messages_4953_ = crate::leanh::lean_ctor_get(v___x_4947_, 6);
                v_infoState_4954_ = crate::leanh::lean_ctor_get(v___x_4947_, 7);
                v_snapshotTasks_4955_ = crate::leanh::lean_ctor_get(v___x_4947_, 8);
                v_isSharedCheck_5009_ = (!crate::leanh::lean_is_exclusive(v___x_4947_)) as u8;
                if v_isSharedCheck_5009_ == 0 {
                    v_unused_5010_ = crate::leanh::lean_ctor_get(v___x_4947_, 5);
                    crate::leanh::lean_dec(v_unused_5010_);
                    v___x_4957_ = v___x_4947_;
                    v_isShared_4958_ = v_isSharedCheck_5009_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4955_);
                    crate::leanh::lean_inc(v_infoState_4954_);
                    crate::leanh::lean_inc(v_messages_4953_);
                    crate::leanh::lean_inc(v_traceState_4952_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4951_);
                    crate::leanh::lean_inc(v_ngen_4950_);
                    crate::leanh::lean_inc(v_nextMacroScope_4949_);
                    crate::leanh::lean_inc(v_env_4948_);
                    crate::leanh::lean_dec(v___x_4947_);
                    v___x_4957_ = crate::leanh::lean_box(0);
                    v_isShared_4958_ = v_isSharedCheck_5009_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4959_ = l_Lean_Environment_setExporting(v_env_4948_, v_isExporting_4938_);
                v___x_4960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__2);
                if v_isShared_4958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4957_, 5, v___x_4960_);
                    crate::leanh::lean_ctor_set(v___x_4957_, 0, v___x_4959_);
                    v___x_4962_ = v___x_4957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5008_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 0, v___x_4959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 1, v_nextMacroScope_4949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 2, v_ngen_4950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 3, v_auxDeclNGen_4951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 4, v_traceState_4952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 5, v___x_4960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 6, v_messages_4953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 7, v_infoState_4954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5008_, 8, v_snapshotTasks_4955_);
                    v___x_4962_ = v_reuseFailAlloc_5008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4963_ = lean_st_ref_set(v___y_4942_, v___x_4962_);
                v___x_4964_ = lean_st_ref_take(v___y_4940_);
                v_mctx_4965_ = crate::leanh::lean_ctor_get(v___x_4964_, 0);
                v_zetaDeltaFVarIds_4966_ = crate::leanh::lean_ctor_get(v___x_4964_, 2);
                v_postponed_4967_ = crate::leanh::lean_ctor_get(v___x_4964_, 3);
                v_diag_4968_ = crate::leanh::lean_ctor_get(v___x_4964_, 4);
                v_isSharedCheck_5006_ = (!crate::leanh::lean_is_exclusive(v___x_4964_)) as u8;
                if v_isSharedCheck_5006_ == 0 {
                    v_unused_5007_ = crate::leanh::lean_ctor_get(v___x_4964_, 1);
                    crate::leanh::lean_dec(v_unused_5007_);
                    v___x_4970_ = v___x_4964_;
                    v_isShared_4971_ = v_isSharedCheck_5006_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4968_);
                    crate::leanh::lean_inc(v_postponed_4967_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4966_);
                    crate::leanh::lean_inc(v_mctx_4965_);
                    crate::leanh::lean_dec(v___x_4964_);
                    v___x_4970_ = crate::leanh::lean_box(0);
                    v_isShared_4971_ = v_isSharedCheck_5006_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4972_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg___closed__3);
                if v_isShared_4971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4970_, 1, v___x_4972_);
                    v___x_4974_ = v___x_4970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_mctx_4965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___x_4972_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5005_,
                        2,
                        v_zetaDeltaFVarIds_4966_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 3, v_postponed_4967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5005_, 4, v_diag_4968_);
                    v___x_4974_ = v_reuseFailAlloc_5005_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4975_ = lean_st_ref_set(v___y_4940_, v___x_4974_);
                crate::leanh::lean_inc(v___y_4942_);
                crate::leanh::lean_inc_ref(v___y_4941_);
                crate::leanh::lean_inc(v___y_4940_);
                crate::leanh::lean_inc_ref(v___y_4939_);
                v_r_4976_ = crate::leanh::lean_apply_5(
                    v_x_4937_,
                    v___y_4939_,
                    v___y_4940_,
                    v___y_4941_,
                    v___y_4942_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_4976_) == 0 {
                    v_a_4977_ = crate::leanh::lean_ctor_get(v_r_4976_, 0);
                    v_isSharedCheck_4993_ = (!crate::leanh::lean_is_exclusive(v_r_4976_)) as u8;
                    if v_isSharedCheck_4993_ == 0 {
                        v___x_4979_ = v_r_4976_;
                        v_isShared_4980_ = v_isSharedCheck_4993_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4977_);
                        crate::leanh::lean_dec(v_r_4976_);
                        v___x_4979_ = crate::leanh::lean_box(0);
                        v_isShared_4980_ = v_isSharedCheck_4993_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_4994_ = crate::leanh::lean_ctor_get(v_r_4976_, 0);
                    crate::leanh::lean_inc(v_a_4994_);
                    crate::leanh::lean_dec_ref_known(v_r_4976_, 1);
                    v___x_4995_ = crate::leanh::lean_box(0);
                    v___x_4996_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_4942_, v_isExporting_4946_, v___x_4960_, v___y_4940_, v___x_4972_, v___x_4995_);
                    v_isSharedCheck_5003_ = (!crate::leanh::lean_is_exclusive(v___x_4996_)) as u8;
                    if v_isSharedCheck_5003_ == 0 {
                        v_unused_5004_ = crate::leanh::lean_ctor_get(v___x_4996_, 0);
                        crate::leanh::lean_dec(v_unused_5004_);
                        v___x_4998_ = v___x_4996_;
                        v_isShared_4999_ = v_isSharedCheck_5003_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4996_);
                        v___x_4998_ = crate::leanh::lean_box(0);
                        v_isShared_4999_ = v_isSharedCheck_5003_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_4977_);
                if v_isShared_4980_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4979_, 1);
                    v___x_4982_ = v___x_4979_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4992_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4977_);
                    v___x_4982_ = v_reuseFailAlloc_4992_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4983_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___lam__0(v___y_4942_, v_isExporting_4946_, v___x_4960_, v___y_4940_, v___x_4972_, v___x_4982_);
                crate::leanh::lean_dec_ref(v___x_4982_);
                v_isSharedCheck_4990_ = (!crate::leanh::lean_is_exclusive(v___x_4983_)) as u8;
                if v_isSharedCheck_4990_ == 0 {
                    v_unused_4991_ = crate::leanh::lean_ctor_get(v___x_4983_, 0);
                    crate::leanh::lean_dec(v_unused_4991_);
                    v___x_4985_ = v___x_4983_;
                    v_isShared_4986_ = v_isSharedCheck_4990_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4983_);
                    v___x_4985_ = crate::leanh::lean_box(0);
                    v_isShared_4986_ = v_isSharedCheck_4990_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4986_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4985_, 0, v_a_4977_);
                    v___x_4988_ = v___x_4985_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4977_);
                    v___x_4988_ = v_reuseFailAlloc_4989_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4988_;
            }
            9 => {
                if v_isShared_4999_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4998_, 1);
                    crate::leanh::lean_ctor_set(v___x_4998_, 0, v_a_4994_);
                    v___x_5001_ = v___x_4998_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4994_);
                    v___x_5001_ = v_reuseFailAlloc_5002_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg___boxed(
    mut v_x_5011_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
    mut v___y_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_5018_: u8 = 0;
    let mut v_res_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5018_ = (crate::leanh::lean_unbox(v_isExporting_5012_) as u8);
    v_res_5019_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_5011_, v_isExporting_boxed_5018_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
    crate::leanh::lean_dec(v___y_5016_);
    crate::leanh::lean_dec_ref(v___y_5015_);
    crate::leanh::lean_dec(v___y_5014_);
    crate::leanh::lean_dec_ref(v___y_5013_);
    return v_res_5019_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(
    mut v_x_5020_: *mut crate::leanh::LeanObject,
    mut v_when_5021_: u8,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_5021_ == 0 {
        let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_5025_);
        crate::leanh::lean_inc_ref(v___y_5024_);
        crate::leanh::lean_inc(v___y_5023_);
        crate::leanh::lean_inc_ref(v___y_5022_);
        v___x_5027_ = crate::leanh::lean_apply_5(
            v_x_5020_,
            v___y_5022_,
            v___y_5023_,
            v___y_5024_,
            v___y_5025_,
            crate::leanh::lean_box(0),
        );
        return v___x_5027_;
    } else {
        let mut v___x_5028_: u8 = 0;
        let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5028_ = 0;
        v___x_5029_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_5020_, v___x_5028_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
        return v___x_5029_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg___boxed(
    mut v_x_5030_: *mut crate::leanh::LeanObject,
    mut v_when_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_5037_: u8 = 0;
    let mut v_res_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_5037_ = (crate::leanh::lean_unbox(v_when_5031_) as u8);
    v_res_5038_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(
        v_x_5030_,
        v_when_boxed_5037_,
        v___y_5032_,
        v___y_5033_,
        v___y_5034_,
        v___y_5035_,
    );
    crate::leanh::lean_dec(v___y_5035_);
    crate::leanh::lean_dec_ref(v___y_5034_);
    crate::leanh::lean_dec(v___y_5033_);
    crate::leanh::lean_dec_ref(v___y_5032_);
    return v_res_5038_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(
    mut v_upperBound_5039_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5040_: *mut crate::leanh::LeanObject,
    mut v___x_5041_: *mut crate::leanh::LeanObject,
    mut v___x_5042_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5043_: u8,
    mut v___x_5044_: *mut crate::leanh::LeanObject,
    mut v_params_5045_: *mut crate::leanh::LeanObject,
    mut v_self_5046_: *mut crate::leanh::LeanObject,
    mut v_a_5047_: *mut crate::leanh::LeanObject,
    mut v___x_5048_: *mut crate::leanh::LeanObject,
    mut v_n_5049_: *mut crate::leanh::LeanObject,
    mut v___x_5050_: *mut crate::leanh::LeanObject,
    mut v_a_5051_: u8,
    mut v_a_5052_: *mut crate::leanh::LeanObject,
    mut v_b_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
    mut v___y_5056_: *mut crate::leanh::LeanObject,
    mut v___y_5057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5059_: u8 = 0;
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_projName_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfoOverrides_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: u8 = 0;
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5059_ = lean_nat_dec_lt(v_a_5052_, v_upperBound_5039_);
                if v___x_5059_ == 0 {
                    crate::leanh::lean_dec(v_a_5052_);
                    crate::leanh::lean_dec(v___x_5050_);
                    crate::leanh::lean_dec(v_n_5049_);
                    crate::leanh::lean_dec_ref(v___x_5048_);
                    crate::leanh::lean_dec_ref(v_a_5047_);
                    crate::leanh::lean_dec_ref(v_self_5046_);
                    crate::leanh::lean_dec_ref(v_params_5045_);
                    crate::leanh::lean_dec(v___x_5044_);
                    crate::leanh::lean_dec(v___x_5042_);
                    crate::leanh::lean_dec_ref(v___x_5041_);
                    v___x_5060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5060_, 0, v_b_5053_);
                    return v___x_5060_;
                } else {
                    v___x_5061_ = lean_array_fget_borrowed(v_projDecls_5040_, v_a_5052_);
                    v_ref_5062_ = crate::leanh::lean_ctor_get(v___x_5061_, 0);
                    v_projName_5063_ = crate::leanh::lean_ctor_get(v___x_5061_, 1);
                    v_paramInfoOverrides_5064_ = crate::leanh::lean_ctor_get(v___x_5061_, 2);
                    v___x_5065_ = crate::leanh::lean_box((v_instImplicit_5043_) as usize);
                    v___x_5066_ = crate::leanh::lean_box((v___x_5059_) as usize);
                    v___x_5067_ = crate::leanh::lean_box((v_a_5051_) as usize);
                    crate::leanh::lean_inc(v___x_5050_);
                    crate::leanh::lean_inc_n(v_ref_5062_, 2);
                    crate::leanh::lean_inc_n(v_n_5049_, 2);
                    crate::leanh::lean_inc(v_paramInfoOverrides_5064_);
                    crate::leanh::lean_inc_ref(v___x_5048_);
                    crate::leanh::lean_inc_ref(v_a_5047_);
                    crate::leanh::lean_inc_ref(v_b_5053_);
                    crate::leanh::lean_inc_ref(v_self_5046_);
                    crate::leanh::lean_inc_ref(v_params_5045_);
                    crate::leanh::lean_inc(v___x_5044_);
                    crate::leanh::lean_inc(v_a_5052_);
                    crate::leanh::lean_inc(v___x_5042_);
                    crate::leanh::lean_inc_n(v_projName_5063_, 2);
                    crate::leanh::lean_inc_ref(v___x_5041_);
                    v___f_5068_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 23, 17);
                    crate::leanh::lean_closure_set(v___f_5068_, 0, v___x_5041_);
                    crate::leanh::lean_closure_set(v___f_5068_, 1, v_projName_5063_);
                    crate::leanh::lean_closure_set(v___f_5068_, 2, v___x_5042_);
                    crate::leanh::lean_closure_set(v___f_5068_, 3, v_a_5052_);
                    crate::leanh::lean_closure_set(v___f_5068_, 4, v___x_5065_);
                    crate::leanh::lean_closure_set(v___f_5068_, 5, v___x_5044_);
                    crate::leanh::lean_closure_set(v___f_5068_, 6, v_params_5045_);
                    crate::leanh::lean_closure_set(v___f_5068_, 7, v_self_5046_);
                    crate::leanh::lean_closure_set(v___f_5068_, 8, v_b_5053_);
                    crate::leanh::lean_closure_set(v___f_5068_, 9, v___x_5066_);
                    crate::leanh::lean_closure_set(v___f_5068_, 10, v_a_5047_);
                    crate::leanh::lean_closure_set(v___f_5068_, 11, v___x_5048_);
                    crate::leanh::lean_closure_set(v___f_5068_, 12, v_paramInfoOverrides_5064_);
                    crate::leanh::lean_closure_set(v___f_5068_, 13, v_n_5049_);
                    crate::leanh::lean_closure_set(v___f_5068_, 14, v_ref_5062_);
                    crate::leanh::lean_closure_set(v___f_5068_, 15, v___x_5050_);
                    crate::leanh::lean_closure_set(v___f_5068_, 16, v___x_5067_);
                    v___x_5069_ = l_Lean_Expr_isForall(v_b_5053_);
                    crate::leanh::lean_dec_ref(v_b_5053_);
                    v___x_5070_ = crate::leanh::lean_box((v___x_5069_) as usize);
                    v___y_5071_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 5);
                    crate::leanh::lean_closure_set(v___y_5071_, 0, v___x_5070_);
                    crate::leanh::lean_closure_set(v___y_5071_, 1, v_projName_5063_);
                    crate::leanh::lean_closure_set(v___y_5071_, 2, v_n_5049_);
                    crate::leanh::lean_closure_set(v___y_5071_, 3, v_ref_5062_);
                    crate::leanh::lean_closure_set(v___y_5071_, 4, v___f_5068_);
                    v___x_5072_ = l_Lean_isPrivateName(v_projName_5063_);
                    v___x_5073_ =
                        l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(
                            v___y_5071_,
                            v___x_5072_,
                            v___y_5054_,
                            v___y_5055_,
                            v___y_5056_,
                            v___y_5057_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5073_) == 0 {
                        v_a_5074_ = crate::leanh::lean_ctor_get(v___x_5073_, 0);
                        crate::leanh::lean_inc(v_a_5074_);
                        crate::leanh::lean_dec_ref_known(v___x_5073_, 1);
                        v___x_5075_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5076_ = lean_nat_add(v_a_5052_, v___x_5075_);
                        crate::leanh::lean_dec(v_a_5052_);
                        v_a_5052_ = v___x_5076_;
                        v_b_5053_ = v_a_5074_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5052_);
                        crate::leanh::lean_dec(v___x_5050_);
                        crate::leanh::lean_dec(v_n_5049_);
                        crate::leanh::lean_dec_ref(v___x_5048_);
                        crate::leanh::lean_dec_ref(v_a_5047_);
                        crate::leanh::lean_dec_ref(v_self_5046_);
                        crate::leanh::lean_dec_ref(v_params_5045_);
                        crate::leanh::lean_dec(v___x_5044_);
                        crate::leanh::lean_dec(v___x_5042_);
                        crate::leanh::lean_dec_ref(v___x_5041_);
                        return v___x_5073_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_5078_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_projDecls_5079_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_5080_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5081_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_instImplicit_5082_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5083_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_params_5084_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_self_5085_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_5086_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5087_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_n_5088_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_5089_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_5090_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_5091_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_b_5092_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5093_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5094_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5095_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5096_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5097_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_instImplicit_boxed_5098_: u8 = 0;
    let mut v_a_19509__boxed_5099_: u8 = 0;
    let mut v_res_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5098_ = (crate::leanh::lean_unbox(v_instImplicit_5082_) as u8);
    v_a_19509__boxed_5099_ = (crate::leanh::lean_unbox(v_a_5090_) as u8);
    v_res_5100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(
        v_upperBound_5078_,
        v_projDecls_5079_,
        v___x_5080_,
        v___x_5081_,
        v_instImplicit_boxed_5098_,
        v___x_5083_,
        v_params_5084_,
        v_self_5085_,
        v_a_5086_,
        v___x_5087_,
        v_n_5088_,
        v___x_5089_,
        v_a_19509__boxed_5099_,
        v_a_5091_,
        v_b_5092_,
        v___y_5093_,
        v___y_5094_,
        v___y_5095_,
        v___y_5096_,
    );
    crate::leanh::lean_dec(v___y_5096_);
    crate::leanh::lean_dec_ref(v___y_5095_);
    crate::leanh::lean_dec(v___y_5094_);
    crate::leanh::lean_dec_ref(v___y_5093_);
    crate::leanh::lean_dec_ref(v_projDecls_5079_);
    crate::leanh::lean_dec(v_upperBound_5078_);
    return v_res_5100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(
    mut v_instImplicit_5101_: u8,
    mut v_as_5102_: *mut crate::leanh::LeanObject,
    mut v_sz_5103_: usize,
    mut v_i_5104_: usize,
    mut v_b_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: usize = 0;
    let mut v___x_5119_: usize = 0;
    let mut v___y_5122_: u8 = 0;
    let mut v___x_5123_: u8 = 0;
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: u8 = 0;
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: u8 = 0;
    let mut v___x_5130_: u8 = 0;
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5135_: u8 = 0;
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5110_ = lean_usize_dec_lt(v_i_5104_, v_sz_5103_);
                if v___x_5110_ == 0 {
                    v___x_5111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5111_, 0, v_b_5105_);
                    return v___x_5111_;
                } else {
                    v_a_5112_ = lean_array_uget_borrowed(v_as_5102_, v_i_5104_);
                    v___x_5113_ = l_Lean_Expr_fvarId_x21(v_a_5112_);
                    crate::leanh::lean_inc(v___x_5113_);
                    v___x_5114_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_5113_,
                        v___y_5106_,
                        v___y_5107_,
                        v___y_5108_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5114_) == 0 {
                        v_a_5115_ = crate::leanh::lean_ctor_get(v___x_5114_, 0);
                        crate::leanh::lean_inc(v_a_5115_);
                        crate::leanh::lean_dec_ref_known(v___x_5114_, 1);
                        v___x_5125_ = l_Lean_LocalDecl_binderInfo(v_a_5115_);
                        v___x_5126_ = l_Lean_BinderInfo_isInstImplicit(v___x_5125_);
                        if v___x_5126_ == 0 {
                            v___x_5128_ = l_Lean_LocalDecl_type(v_a_5115_);
                            crate::leanh::lean_dec(v_a_5115_);
                            v___x_5129_ = lean_is_out_param(v___x_5128_);
                            if v___x_5129_ == 0 {
                                v___x_5130_ = 0;
                                v___x_5131_ = l_Lean_LocalContext_setBinderInfo(
                                    v_b_5105_,
                                    v___x_5113_,
                                    v___x_5130_,
                                );
                                v_a_5117_ = v___x_5131_;
                                state = 1;
                                continue;
                            } else {
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5115_);
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5113_);
                        crate::leanh::lean_dec_ref(v_b_5105_);
                        v_a_5132_ = crate::leanh::lean_ctor_get(v___x_5114_, 0);
                        v_isSharedCheck_5139_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5114_)) as u8;
                        if v_isSharedCheck_5139_ == 0 {
                            v___x_5134_ = v___x_5114_;
                            v_isShared_5135_ = v_isSharedCheck_5139_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5132_);
                            crate::leanh::lean_dec(v___x_5114_);
                            v___x_5134_ = crate::leanh::lean_box(0);
                            v_isShared_5135_ = v_isSharedCheck_5139_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5118_ = 1usize;
                v___x_5119_ = lean_usize_add(v_i_5104_, v___x_5118_);
                v_i_5104_ = v___x_5119_;
                v_b_5105_ = v_a_5117_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_5122_ == 0 {
                    crate::leanh::lean_dec(v___x_5113_);
                    v_a_5117_ = v_b_5105_;
                    state = 1;
                    continue;
                } else {
                    v___x_5123_ = 1;
                    v___x_5124_ =
                        l_Lean_LocalContext_setBinderInfo(v_b_5105_, v___x_5113_, v___x_5123_);
                    v_a_5117_ = v___x_5124_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___x_5126_ == 0 {
                    v___y_5122_ = v___x_5126_;
                    state = 2;
                    continue;
                } else {
                    v___y_5122_ = v_instImplicit_5101_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v_isShared_5135_ == 0 {
                    v___x_5137_ = v___x_5134_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
                    v___x_5137_ = v_reuseFailAlloc_5138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg___boxed(
    mut v_instImplicit_5140_: *mut crate::leanh::LeanObject,
    mut v_as_5141_: *mut crate::leanh::LeanObject,
    mut v_sz_5142_: *mut crate::leanh::LeanObject,
    mut v_i_5143_: *mut crate::leanh::LeanObject,
    mut v_b_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_instImplicit_boxed_5149_: u8 = 0;
    let mut v_sz_boxed_5150_: usize = 0;
    let mut v_i_boxed_5151_: usize = 0;
    let mut v_res_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5149_ = (crate::leanh::lean_unbox(v_instImplicit_5140_) as u8);
    v_sz_boxed_5150_ = crate::leanh::lean_unbox_usize(v_sz_5142_);
    crate::leanh::lean_dec(v_sz_5142_);
    v_i_boxed_5151_ = crate::leanh::lean_unbox_usize(v_i_5143_);
    crate::leanh::lean_dec(v_i_5143_);
    v_res_5152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_boxed_5149_, v_as_5141_, v_sz_boxed_5150_, v_i_boxed_5151_, v_b_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
    crate::leanh::lean_dec(v___y_5147_);
    crate::leanh::lean_dec_ref(v___y_5146_);
    crate::leanh::lean_dec_ref(v___y_5145_);
    crate::leanh::lean_dec_ref(v_as_5141_);
    return v_res_5152_;
}
pub unsafe fn l_Lean_Meta_mkProjections___lam__0(
    mut v_params_5153_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5154_: u8,
    mut v_projDecls_5155_: *mut crate::leanh::LeanObject,
    mut v_toConstantVal_5156_: *mut crate::leanh::LeanObject,
    mut v_numParams_5157_: *mut crate::leanh::LeanObject,
    mut v___x_5158_: *mut crate::leanh::LeanObject,
    mut v_n_5159_: *mut crate::leanh::LeanObject,
    mut v_levelParams_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: u8,
    mut v_ctorType_5162_: *mut crate::leanh::LeanObject,
    mut v_self_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5171_: usize = 0;
    let mut v___x_5172_: usize = 0;
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_unused_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v_a_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_5169_ = crate::leanh::lean_ctor_get(v___y_5164_, 2);
                crate::leanh::lean_inc_ref(v_self_5163_);
                crate::leanh::lean_inc_ref(v_params_5153_);
                v___x_5170_ = lean_array_push(v_params_5153_, v_self_5163_);
                v_sz_5171_ = lean_array_size(v_params_5153_);
                v___x_5172_ = 0usize;
                crate::leanh::lean_inc_ref(v_lctx_5169_);
                v___x_5173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_5154_, v_params_5153_, v_sz_5171_, v___x_5172_, v_lctx_5169_, v___y_5164_, v___y_5166_, v___y_5167_);
                if crate::leanh::lean_obj_tag(v___x_5173_) == 0 {
                    v_a_5174_ = crate::leanh::lean_ctor_get(v___x_5173_, 0);
                    crate::leanh::lean_inc(v_a_5174_);
                    crate::leanh::lean_dec_ref_known(v___x_5173_, 1);
                    v___x_5175_ = lean_array_get_size(v_projDecls_5155_);
                    v___x_5176_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(v___x_5175_, v_projDecls_5155_, v_toConstantVal_5156_, v_numParams_5157_, v_instImplicit_5154_, v___x_5158_, v_params_5153_, v_self_5163_, v_a_5174_, v___x_5170_, v_n_5159_, v_levelParams_5160_, v_a_5161_, v___x_5176_, v_ctorType_5162_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_);
                    if crate::leanh::lean_obj_tag(v___x_5177_) == 0 {
                        v_isSharedCheck_5185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5177_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v_unused_5186_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                            crate::leanh::lean_dec(v_unused_5186_);
                            v___x_5179_ = v___x_5177_;
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5177_);
                            v___x_5179_ = crate::leanh::lean_box(0);
                            v_isShared_5180_ = v_isSharedCheck_5185_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5187_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                        v_isSharedCheck_5194_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5177_)) as u8;
                        if v_isSharedCheck_5194_ == 0 {
                            v___x_5189_ = v___x_5177_;
                            v_isShared_5190_ = v_isSharedCheck_5194_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5187_);
                            crate::leanh::lean_dec(v___x_5177_);
                            v___x_5189_ = crate::leanh::lean_box(0);
                            v_isShared_5190_ = v_isSharedCheck_5194_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5170_);
                    crate::leanh::lean_dec_ref(v_self_5163_);
                    crate::leanh::lean_dec_ref(v_ctorType_5162_);
                    crate::leanh::lean_dec(v_levelParams_5160_);
                    crate::leanh::lean_dec(v_n_5159_);
                    crate::leanh::lean_dec(v___x_5158_);
                    crate::leanh::lean_dec(v_numParams_5157_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_5156_);
                    crate::leanh::lean_dec_ref(v_params_5153_);
                    v_a_5195_ = crate::leanh::lean_ctor_get(v___x_5173_, 0);
                    v_isSharedCheck_5202_ = (!crate::leanh::lean_is_exclusive(v___x_5173_)) as u8;
                    if v_isSharedCheck_5202_ == 0 {
                        v___x_5197_ = v___x_5173_;
                        v_isShared_5198_ = v_isSharedCheck_5202_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5195_);
                        crate::leanh::lean_dec(v___x_5173_);
                        v___x_5197_ = crate::leanh::lean_box(0);
                        v_isShared_5198_ = v_isSharedCheck_5202_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5181_ = crate::leanh::lean_box(0);
                if v_isShared_5180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5179_, 0, v___x_5181_);
                    v___x_5183_ = v___x_5179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
                    v___x_5183_ = v_reuseFailAlloc_5184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5183_;
            }
            3 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5192_;
            }
            5 => {
                if v_isShared_5198_ == 0 {
                    v___x_5200_ = v___x_5197_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
                    v___x_5200_ = v_reuseFailAlloc_5201_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkProjections___lam__0___boxed(
    mut v_params_5203_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5204_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5205_: *mut crate::leanh::LeanObject,
    mut v_toConstantVal_5206_: *mut crate::leanh::LeanObject,
    mut v_numParams_5207_: *mut crate::leanh::LeanObject,
    mut v___x_5208_: *mut crate::leanh::LeanObject,
    mut v_n_5209_: *mut crate::leanh::LeanObject,
    mut v_levelParams_5210_: *mut crate::leanh::LeanObject,
    mut v_a_5211_: *mut crate::leanh::LeanObject,
    mut v_ctorType_5212_: *mut crate::leanh::LeanObject,
    mut v_self_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
    mut v___y_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_instImplicit_boxed_5219_: u8 = 0;
    let mut v_a_19651__boxed_5220_: u8 = 0;
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5219_ = (crate::leanh::lean_unbox(v_instImplicit_5204_) as u8);
    v_a_19651__boxed_5220_ = (crate::leanh::lean_unbox(v_a_5211_) as u8);
    v_res_5221_ = l_Lean_Meta_mkProjections___lam__0(
        v_params_5203_,
        v_instImplicit_boxed_5219_,
        v_projDecls_5205_,
        v_toConstantVal_5206_,
        v_numParams_5207_,
        v___x_5208_,
        v_n_5209_,
        v_levelParams_5210_,
        v_a_19651__boxed_5220_,
        v_ctorType_5212_,
        v_self_5213_,
        v___y_5214_,
        v___y_5215_,
        v___y_5216_,
        v___y_5217_,
    );
    crate::leanh::lean_dec(v___y_5217_);
    crate::leanh::lean_dec_ref(v___y_5216_);
    crate::leanh::lean_dec(v___y_5215_);
    crate::leanh::lean_dec_ref(v___y_5214_);
    crate::leanh::lean_dec_ref(v_projDecls_5205_);
    return v_res_5221_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___lam__1___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = l_Lean_Meta_mkProjections___lam__1___closed__2;
    v___x_5227_ = l_Lean_stringToMessageData(v___x_5226_);
    return v___x_5227_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___lam__1___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5229_ = l_Lean_Meta_mkProjections___lam__1___closed__4;
    v___x_5230_ = l_Lean_stringToMessageData(v___x_5229_);
    return v___x_5230_;
}
pub unsafe fn l_Lean_Meta_mkProjections___lam__1(
    mut v_instImplicit_5231_: u8,
    mut v_projDecls_5232_: *mut crate::leanh::LeanObject,
    mut v_toConstantVal_5233_: *mut crate::leanh::LeanObject,
    mut v_numParams_5234_: *mut crate::leanh::LeanObject,
    mut v___x_5235_: *mut crate::leanh::LeanObject,
    mut v_n_5236_: *mut crate::leanh::LeanObject,
    mut v_levelParams_5237_: *mut crate::leanh::LeanObject,
    mut v_a_5238_: u8,
    mut v_params_5239_: *mut crate::leanh::LeanObject,
    mut v_ctorType_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
    mut v___y_5243_: *mut crate::leanh::LeanObject,
    mut v___y_5244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5253_: u8 = 0;
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: u8 = 0;
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: u8 = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: u8 = 0;
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5257_ = crate::leanh::lean_box((v_instImplicit_5231_) as usize);
                v___x_5258_ = crate::leanh::lean_box((v_a_5238_) as usize);
                crate::leanh::lean_inc(v_n_5236_);
                crate::leanh::lean_inc(v___x_5235_);
                crate::leanh::lean_inc(v_numParams_5234_);
                crate::leanh::lean_inc_ref(v_params_5239_);
                v___f_5259_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_mkProjections___lam__0___boxed as *mut core::ffi::c_void,
                    16,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_5259_, 0, v_params_5239_);
                crate::leanh::lean_closure_set(v___f_5259_, 1, v___x_5257_);
                crate::leanh::lean_closure_set(v___f_5259_, 2, v_projDecls_5232_);
                crate::leanh::lean_closure_set(v___f_5259_, 3, v_toConstantVal_5233_);
                crate::leanh::lean_closure_set(v___f_5259_, 4, v_numParams_5234_);
                crate::leanh::lean_closure_set(v___f_5259_, 5, v___x_5235_);
                crate::leanh::lean_closure_set(v___f_5259_, 6, v_n_5236_);
                crate::leanh::lean_closure_set(v___f_5259_, 7, v_levelParams_5237_);
                crate::leanh::lean_closure_set(v___f_5259_, 8, v___x_5258_);
                crate::leanh::lean_closure_set(v___f_5259_, 9, v_ctorType_5240_);
                v___x_5265_ = lean_array_get_size(v_params_5239_);
                v___x_5266_ = lean_nat_dec_eq(v___x_5265_, v_numParams_5234_);
                crate::leanh::lean_dec(v_numParams_5234_);
                if v___x_5266_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_5259_);
                    crate::leanh::lean_dec_ref(v_params_5239_);
                    crate::leanh::lean_dec(v___x_5235_);
                    v___x_5267_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___lam__1___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkProjections___lam__1___closed__3_once
                        ),
                        _init_l_Lean_Meta_mkProjections___lam__1___closed__3,
                    );
                    v___x_5268_ = l_Lean_MessageData_ofConstName(v_n_5236_, v___x_5266_);
                    v___x_5269_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5269_, 0, v___x_5267_);
                    crate::leanh::lean_ctor_set(v___x_5269_, 1, v___x_5268_);
                    v___x_5270_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___lam__1___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_mkProjections___lam__1___closed__5_once
                        ),
                        _init_l_Lean_Meta_mkProjections___lam__1___closed__5,
                    );
                    v___x_5271_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5271_, 0, v___x_5269_);
                    crate::leanh::lean_ctor_set(v___x_5271_, 1, v___x_5270_);
                    v___x_5272_ =
                        l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
                            v___x_5271_,
                            v___y_5241_,
                            v___y_5242_,
                            v___y_5243_,
                            v___y_5244_,
                        );
                    return v___x_5272_;
                } else {
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5254_ = l_Lean_Meta_mkProjections___lam__1___closed__1;
                v___x_5255_ = 0;
                v___x_5256_ =
                    l_Lean_Meta_withLocalDecl___at___00Lean_Meta_mkProjections_spec__9___redArg(
                        v___x_5254_,
                        v___y_5253_,
                        v___y_5252_,
                        v___y_5248_,
                        v___x_5255_,
                        v___y_5250_,
                        v___y_5249_,
                        v___y_5247_,
                        v___y_5251_,
                    );
                return v___x_5256_;
            }
            2 => {
                v___x_5261_ = l_Lean_Expr_const___override(v_n_5236_, v___x_5235_);
                v___x_5262_ = l_Lean_mkAppN(v___x_5261_, v_params_5239_);
                crate::leanh::lean_dec_ref(v_params_5239_);
                if v_instImplicit_5231_ == 0 {
                    v___x_5263_ = 0;
                    v___y_5247_ = v___y_5243_;
                    v___y_5248_ = v___f_5259_;
                    v___y_5249_ = v___y_5242_;
                    v___y_5250_ = v___y_5241_;
                    v___y_5251_ = v___y_5244_;
                    v___y_5252_ = v___x_5262_;
                    v___y_5253_ = v___x_5263_;
                    state = 1;
                    continue;
                } else {
                    v___x_5264_ = 3;
                    v___y_5247_ = v___y_5243_;
                    v___y_5248_ = v___f_5259_;
                    v___y_5249_ = v___y_5242_;
                    v___y_5250_ = v___y_5241_;
                    v___y_5251_ = v___y_5244_;
                    v___y_5252_ = v___x_5262_;
                    v___y_5253_ = v___x_5264_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkProjections___lam__1___boxed(
    mut v_instImplicit_5273_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5274_: *mut crate::leanh::LeanObject,
    mut v_toConstantVal_5275_: *mut crate::leanh::LeanObject,
    mut v_numParams_5276_: *mut crate::leanh::LeanObject,
    mut v___x_5277_: *mut crate::leanh::LeanObject,
    mut v_n_5278_: *mut crate::leanh::LeanObject,
    mut v_levelParams_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v_params_5281_: *mut crate::leanh::LeanObject,
    mut v_ctorType_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
    mut v___y_5284_: *mut crate::leanh::LeanObject,
    mut v___y_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
    mut v___y_5287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_instImplicit_boxed_5288_: u8 = 0;
    let mut v_a_19755__boxed_5289_: u8 = 0;
    let mut v_res_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5288_ = (crate::leanh::lean_unbox(v_instImplicit_5273_) as u8);
    v_a_19755__boxed_5289_ = (crate::leanh::lean_unbox(v_a_5280_) as u8);
    v_res_5290_ = l_Lean_Meta_mkProjections___lam__1(
        v_instImplicit_boxed_5288_,
        v_projDecls_5274_,
        v_toConstantVal_5275_,
        v_numParams_5276_,
        v___x_5277_,
        v_n_5278_,
        v_levelParams_5279_,
        v_a_19755__boxed_5289_,
        v_params_5281_,
        v_ctorType_5282_,
        v___y_5283_,
        v___y_5284_,
        v___y_5285_,
        v___y_5286_,
    );
    crate::leanh::lean_dec(v___y_5286_);
    crate::leanh::lean_dec_ref(v___y_5285_);
    crate::leanh::lean_dec(v___y_5284_);
    crate::leanh::lean_dec_ref(v___y_5283_);
    return v_res_5290_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5291_) == 0 {
                    v___x_5293_ = l_List_reverse___redArg(v_a_5292_);
                    return v___x_5293_;
                } else {
                    v_head_5294_ = crate::leanh::lean_ctor_get(v_a_5291_, 0);
                    v_tail_5295_ = crate::leanh::lean_ctor_get(v_a_5291_, 1);
                    v_isSharedCheck_5304_ = (!crate::leanh::lean_is_exclusive(v_a_5291_)) as u8;
                    if v_isSharedCheck_5304_ == 0 {
                        v___x_5297_ = v_a_5291_;
                        v_isShared_5298_ = v_isSharedCheck_5304_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5295_);
                        crate::leanh::lean_inc(v_head_5294_);
                        crate::leanh::lean_dec(v_a_5291_);
                        v___x_5297_ = crate::leanh::lean_box(0);
                        v_isShared_5298_ = v_isSharedCheck_5304_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5299_ = l_Lean_mkLevelParam(v_head_5294_);
                if v_isShared_5298_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5297_, 1, v_a_5292_);
                    crate::leanh::lean_ctor_set(v___x_5297_, 0, v___x_5299_);
                    v___x_5301_ = v___x_5297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 1, v_a_5292_);
                    v___x_5301_ = v_reuseFailAlloc_5303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5291_ = v_tail_5295_;
                v_a_5292_ = v___x_5301_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5305_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5305_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(
    mut v_msg_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v_toFunctor_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5328_: u8 = 0;
    let mut v___f_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5345_: u8 = 0;
    let mut v_toFunctor_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___f_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14621__overap_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5371_: u8 = 0;
    let mut v_unused_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5373_: u8 = 0;
    let mut v_unused_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5377_: u8 = 0;
    let mut v_unused_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5379_: u8 = 0;
    let mut v_unused_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5316_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__0);
                v___x_5317_ = l_StateRefT_x27_instMonad___redArg(v___x_5316_);
                v_toApplicative_5318_ = crate::leanh::lean_ctor_get(v___x_5317_, 0);
                v_isSharedCheck_5379_ = (!crate::leanh::lean_is_exclusive(v___x_5317_)) as u8;
                if v_isSharedCheck_5379_ == 0 {
                    v_unused_5380_ = crate::leanh::lean_ctor_get(v___x_5317_, 1);
                    crate::leanh::lean_dec(v_unused_5380_);
                    v___x_5320_ = v___x_5317_;
                    v_isShared_5321_ = v_isSharedCheck_5379_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5318_);
                    crate::leanh::lean_dec(v___x_5317_);
                    v___x_5320_ = crate::leanh::lean_box(0);
                    v_isShared_5321_ = v_isSharedCheck_5379_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5322_ = crate::leanh::lean_ctor_get(v_toApplicative_5318_, 0);
                v_toSeq_5323_ = crate::leanh::lean_ctor_get(v_toApplicative_5318_, 2);
                v_toSeqLeft_5324_ = crate::leanh::lean_ctor_get(v_toApplicative_5318_, 3);
                v_toSeqRight_5325_ = crate::leanh::lean_ctor_get(v_toApplicative_5318_, 4);
                v_isSharedCheck_5377_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5318_)) as u8;
                if v_isSharedCheck_5377_ == 0 {
                    v_unused_5378_ = crate::leanh::lean_ctor_get(v_toApplicative_5318_, 1);
                    crate::leanh::lean_dec(v_unused_5378_);
                    v___x_5327_ = v_toApplicative_5318_;
                    v_isShared_5328_ = v_isSharedCheck_5377_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5325_);
                    crate::leanh::lean_inc(v_toSeqLeft_5324_);
                    crate::leanh::lean_inc(v_toSeq_5323_);
                    crate::leanh::lean_inc(v_toFunctor_5322_);
                    crate::leanh::lean_dec(v_toApplicative_5318_);
                    v___x_5327_ = crate::leanh::lean_box(0);
                    v_isShared_5328_ = v_isSharedCheck_5377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5329_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__1;
                v___f_5330_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_5322_);
                v___f_5331_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5331_, 0, v_toFunctor_5322_);
                v___f_5332_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5332_, 0, v_toFunctor_5322_);
                v___x_5333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5333_, 0, v___f_5331_);
                crate::leanh::lean_ctor_set(v___x_5333_, 1, v___f_5332_);
                v___f_5334_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5334_, 0, v_toSeqRight_5325_);
                v___f_5335_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5335_, 0, v_toSeqLeft_5324_);
                v___f_5336_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5336_, 0, v_toSeq_5323_);
                if v_isShared_5328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5327_, 4, v___f_5334_);
                    crate::leanh::lean_ctor_set(v___x_5327_, 3, v___f_5335_);
                    crate::leanh::lean_ctor_set(v___x_5327_, 2, v___f_5336_);
                    crate::leanh::lean_ctor_set(v___x_5327_, 1, v___f_5329_);
                    crate::leanh::lean_ctor_set(v___x_5327_, 0, v___x_5333_);
                    v___x_5338_ = v___x_5327_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5376_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 1, v___f_5329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 2, v___f_5336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 3, v___f_5335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 4, v___f_5334_);
                    v___x_5338_ = v_reuseFailAlloc_5376_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5320_, 1, v___f_5330_);
                    crate::leanh::lean_ctor_set(v___x_5320_, 0, v___x_5338_);
                    v___x_5340_ = v___x_5320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5375_, 0, v___x_5338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5375_, 1, v___f_5330_);
                    v___x_5340_ = v_reuseFailAlloc_5375_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5341_ = l_StateRefT_x27_instMonad___redArg(v___x_5340_);
                v_toApplicative_5342_ = crate::leanh::lean_ctor_get(v___x_5341_, 0);
                v_isSharedCheck_5373_ = (!crate::leanh::lean_is_exclusive(v___x_5341_)) as u8;
                if v_isSharedCheck_5373_ == 0 {
                    v_unused_5374_ = crate::leanh::lean_ctor_get(v___x_5341_, 1);
                    crate::leanh::lean_dec(v_unused_5374_);
                    v___x_5344_ = v___x_5341_;
                    v_isShared_5345_ = v_isSharedCheck_5373_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5342_);
                    crate::leanh::lean_dec(v___x_5341_);
                    v___x_5344_ = crate::leanh::lean_box(0);
                    v_isShared_5345_ = v_isSharedCheck_5373_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5346_ = crate::leanh::lean_ctor_get(v_toApplicative_5342_, 0);
                v_toSeq_5347_ = crate::leanh::lean_ctor_get(v_toApplicative_5342_, 2);
                v_toSeqLeft_5348_ = crate::leanh::lean_ctor_get(v_toApplicative_5342_, 3);
                v_toSeqRight_5349_ = crate::leanh::lean_ctor_get(v_toApplicative_5342_, 4);
                v_isSharedCheck_5371_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5342_)) as u8;
                if v_isSharedCheck_5371_ == 0 {
                    v_unused_5372_ = crate::leanh::lean_ctor_get(v_toApplicative_5342_, 1);
                    crate::leanh::lean_dec(v_unused_5372_);
                    v___x_5351_ = v_toApplicative_5342_;
                    v_isShared_5352_ = v_isSharedCheck_5371_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5349_);
                    crate::leanh::lean_inc(v_toSeqLeft_5348_);
                    crate::leanh::lean_inc(v_toSeq_5347_);
                    crate::leanh::lean_inc(v_toFunctor_5346_);
                    crate::leanh::lean_dec(v_toApplicative_5342_);
                    v___x_5351_ = crate::leanh::lean_box(0);
                    v_isShared_5352_ = v_isSharedCheck_5371_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5353_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__3;
                v___f_5354_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_5346_);
                v___f_5355_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5355_, 0, v_toFunctor_5346_);
                v___f_5356_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5356_, 0, v_toFunctor_5346_);
                v___x_5357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5357_, 0, v___f_5355_);
                crate::leanh::lean_ctor_set(v___x_5357_, 1, v___f_5356_);
                v___f_5358_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5358_, 0, v_toSeqRight_5349_);
                v___f_5359_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5359_, 0, v_toSeqLeft_5348_);
                v___f_5360_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5360_, 0, v_toSeq_5347_);
                if v_isShared_5352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5351_, 4, v___f_5358_);
                    crate::leanh::lean_ctor_set(v___x_5351_, 3, v___f_5359_);
                    crate::leanh::lean_ctor_set(v___x_5351_, 2, v___f_5360_);
                    crate::leanh::lean_ctor_set(v___x_5351_, 1, v___f_5353_);
                    crate::leanh::lean_ctor_set(v___x_5351_, 0, v___x_5357_);
                    v___x_5362_ = v___x_5351_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5370_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 0, v___x_5357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 1, v___f_5353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 2, v___f_5360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 3, v___f_5359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5370_, 4, v___f_5358_);
                    v___x_5362_ = v_reuseFailAlloc_5370_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5344_, 1, v___f_5354_);
                    crate::leanh::lean_ctor_set(v___x_5344_, 0, v___x_5362_);
                    v___x_5364_ = v___x_5344_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5369_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5369_, 0, v___x_5362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5369_, 1, v___f_5354_);
                    v___x_5364_ = v_reuseFailAlloc_5369_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5365_ = crate::leanh::lean_box(0);
                v___x_5366_ = l_instInhabitedOfMonad___redArg(v___x_5364_, v___x_5365_);
                v___x_14621__overap_5367_ = lean_panic_fn_borrowed(v___x_5366_, v_msg_5310_);
                crate::leanh::lean_dec(v___x_5366_);
                crate::leanh::lean_inc(v___y_5314_);
                crate::leanh::lean_inc_ref(v___y_5313_);
                crate::leanh::lean_inc(v___y_5312_);
                crate::leanh::lean_inc_ref(v___y_5311_);
                v___x_5368_ = crate::leanh::lean_apply_5(
                    v___x_14621__overap_5367_,
                    v___y_5311_,
                    v___y_5312_,
                    v___y_5313_,
                    v___y_5314_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1___boxed(
    mut v_msg_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5387_ =
        l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(
            v_msg_5381_,
            v___y_5382_,
            v___y_5383_,
            v___y_5384_,
            v___y_5385_,
        );
    crate::leanh::lean_dec(v___y_5385_);
    crate::leanh::lean_dec_ref(v___y_5384_);
    crate::leanh::lean_dec(v___y_5383_);
    crate::leanh::lean_dec_ref(v___y_5382_);
    return v_res_5387_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5389_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__0;
    v___x_5390_ = l_Lean_stringToMessageData(v___x_5389_);
    return v___x_5390_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__4;
    v___x_5395_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_5396_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_5397_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__3;
    v___x_5398_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__2;
    v___x_5399_ = l_mkPanicMessageWithDecl(
        v___x_5398_,
        v___x_5397_,
        v___x_5396_,
        v___x_5395_,
        v___x_5394_,
    );
    return v___x_5399_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(
    mut v_constName_5400_: *mut crate::leanh::LeanObject,
    mut v___y_5401_: *mut crate::leanh::LeanObject,
    mut v___y_5402_: *mut crate::leanh::LeanObject,
    mut v___y_5403_: *mut crate::leanh::LeanObject,
    mut v___y_5404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: u8 = 0;
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: u8 = 0;
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_5419_: u8 = 0;
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v_val_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5439_: u8 = 0;
    let mut v_a_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5414_ = lean_st_ref_get(v___y_5404_);
                v_env_5415_ = crate::leanh::lean_ctor_get(v___x_5414_, 0);
                crate::leanh::lean_inc_ref(v_env_5415_);
                crate::leanh::lean_dec(v___x_5414_);
                v___x_5416_ = 0;
                crate::leanh::lean_inc(v_constName_5400_);
                v___x_5417_ =
                    l_Lean_Environment_findAsync_x3f(v_env_5415_, v_constName_5400_, v___x_5416_);
                if crate::leanh::lean_obj_tag(v___x_5417_) == 1 {
                    v_val_5418_ = crate::leanh::lean_ctor_get(v___x_5417_, 0);
                    crate::leanh::lean_inc(v_val_5418_);
                    crate::leanh::lean_dec_ref_known(v___x_5417_, 1);
                    v_kind_5419_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_5418_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_5419_ == 6 {
                        v___x_5420_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_5418_);
                        if crate::leanh::lean_obj_tag(v___x_5420_) == 6 {
                            crate::leanh::lean_dec(v_constName_5400_);
                            v_val_5421_ = crate::leanh::lean_ctor_get(v___x_5420_, 0);
                            v_isSharedCheck_5428_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5420_)) as u8;
                            if v_isSharedCheck_5428_ == 0 {
                                v___x_5423_ = v___x_5420_;
                                v_isShared_5424_ = v_isSharedCheck_5428_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5421_);
                                crate::leanh::lean_dec(v___x_5420_);
                                v___x_5423_ = crate::leanh::lean_box(0);
                                v_isShared_5424_ = v_isSharedCheck_5428_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5420_);
                            v___x_5429_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
                            v___x_5430_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_5429_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
                            if crate::leanh::lean_obj_tag(v___x_5430_) == 0 {
                                v_a_5431_ = crate::leanh::lean_ctor_get(v___x_5430_, 0);
                                v_isSharedCheck_5439_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5430_)) as u8;
                                if v_isSharedCheck_5439_ == 0 {
                                    v___x_5433_ = v___x_5430_;
                                    v_isShared_5434_ = v_isSharedCheck_5439_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5431_);
                                    crate::leanh::lean_dec(v___x_5430_);
                                    v___x_5433_ = crate::leanh::lean_box(0);
                                    v_isShared_5434_ = v_isSharedCheck_5439_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_5400_);
                                v_a_5440_ = crate::leanh::lean_ctor_get(v___x_5430_, 0);
                                v_isSharedCheck_5447_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5430_)) as u8;
                                if v_isSharedCheck_5447_ == 0 {
                                    v___x_5442_ = v___x_5430_;
                                    v_isShared_5443_ = v_isSharedCheck_5447_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5440_);
                                    crate::leanh::lean_dec(v___x_5430_);
                                    v___x_5442_ = crate::leanh::lean_box(0);
                                    v_isShared_5443_ = v_isSharedCheck_5447_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5418_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5417_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5407_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__1_once),
                    _init_l_Lean_Meta_getStructureName___closed__1,
                );
                v___x_5408_ = 0;
                v___x_5409_ = l_Lean_MessageData_ofConstName(v_constName_5400_, v___x_5408_);
                v___x_5410_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5410_, 0, v___x_5407_);
                crate::leanh::lean_ctor_set(v___x_5410_, 1, v___x_5409_);
                v___x_5411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__1);
                v___x_5412_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5410_);
                crate::leanh::lean_ctor_set(v___x_5412_, 1, v___x_5411_);
                v___x_5413_ =
                    l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
                        v___x_5412_,
                        v___y_5401_,
                        v___y_5402_,
                        v___y_5403_,
                        v___y_5404_,
                    );
                return v___x_5413_;
            }
            2 => {
                if v_isShared_5424_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5423_, 0);
                    v___x_5426_ = v___x_5423_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_val_5421_);
                    v___x_5426_ = v_reuseFailAlloc_5427_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5426_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_5431_) == 0 {
                    crate::leanh::lean_del_object(v___x_5433_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_5400_);
                    v_val_5435_ = crate::leanh::lean_ctor_get(v_a_5431_, 0);
                    crate::leanh::lean_inc(v_val_5435_);
                    crate::leanh::lean_dec_ref_known(v_a_5431_, 1);
                    if v_isShared_5434_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5433_, 0, v_val_5435_);
                        v___x_5437_ = v___x_5433_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_val_5435_);
                        v___x_5437_ = v_reuseFailAlloc_5438_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5437_;
            }
            6 => {
                if v_isShared_5443_ == 0 {
                    v___x_5445_ = v___x_5442_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5440_);
                    v___x_5445_ = v_reuseFailAlloc_5446_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___boxed(
    mut v_constName_5448_: *mut crate::leanh::LeanObject,
    mut v___y_5449_: *mut crate::leanh::LeanObject,
    mut v___y_5450_: *mut crate::leanh::LeanObject,
    mut v___y_5451_: *mut crate::leanh::LeanObject,
    mut v___y_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(
        v_constName_5448_,
        v___y_5449_,
        v___y_5450_,
        v___y_5451_,
        v___y_5452_,
    );
    crate::leanh::lean_dec(v___y_5452_);
    crate::leanh::lean_dec_ref(v___y_5451_);
    crate::leanh::lean_dec(v___y_5450_);
    crate::leanh::lean_dec_ref(v___y_5449_);
    return v_res_5454_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5456_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__0;
    v___x_5457_ = l_Lean_stringToMessageData(v___x_5456_);
    return v___x_5457_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(
    mut v_constName_5458_: *mut crate::leanh::LeanObject,
    mut v___y_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: u8 = 0;
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5464_ = lean_st_ref_get(v___y_5462_);
                v_env_5465_ = crate::leanh::lean_ctor_get(v___x_5464_, 0);
                crate::leanh::lean_inc_ref(v_env_5465_);
                crate::leanh::lean_dec(v___x_5464_);
                crate::leanh::lean_inc(v_constName_5458_);
                v___x_5466_ = l_Lean_isInductiveCore_x3f(v_env_5465_, v_constName_5458_);
                if crate::leanh::lean_obj_tag(v___x_5466_) == 0 {
                    v___x_5467_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_getStructureName___closed__1_once),
                        _init_l_Lean_Meta_getStructureName___closed__1,
                    );
                    v___x_5468_ = 0;
                    v___x_5469_ = l_Lean_MessageData_ofConstName(v_constName_5458_, v___x_5468_);
                    v___x_5470_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5470_, 0, v___x_5467_);
                    crate::leanh::lean_ctor_set(v___x_5470_, 1, v___x_5469_);
                    v___x_5471_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___closed__1);
                    v___x_5472_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5472_, 0, v___x_5470_);
                    crate::leanh::lean_ctor_set(v___x_5472_, 1, v___x_5471_);
                    v___x_5473_ =
                        l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
                            v___x_5472_,
                            v___y_5459_,
                            v___y_5460_,
                            v___y_5461_,
                            v___y_5462_,
                        );
                    return v___x_5473_;
                } else {
                    crate::leanh::lean_dec(v_constName_5458_);
                    v_val_5474_ = crate::leanh::lean_ctor_get(v___x_5466_, 0);
                    v_isSharedCheck_5481_ = (!crate::leanh::lean_is_exclusive(v___x_5466_)) as u8;
                    if v_isSharedCheck_5481_ == 0 {
                        v___x_5476_ = v___x_5466_;
                        v_isShared_5477_ = v_isSharedCheck_5481_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5474_);
                        crate::leanh::lean_dec(v___x_5466_);
                        v___x_5476_ = crate::leanh::lean_box(0);
                        v_isShared_5477_ = v_isSharedCheck_5481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5477_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5476_, 0);
                    v___x_5479_ = v___x_5476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_val_5474_);
                    v___x_5479_ = v_reuseFailAlloc_5480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0___boxed(
    mut v_constName_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5488_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(
        v_constName_5482_,
        v___y_5483_,
        v___y_5484_,
        v___y_5485_,
        v___y_5486_,
    );
    crate::leanh::lean_dec(v___y_5486_);
    crate::leanh::lean_dec_ref(v___y_5485_);
    crate::leanh::lean_dec(v___y_5484_);
    crate::leanh::lean_dec_ref(v___y_5483_);
    return v_res_5488_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___lam__2___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_Lean_Meta_mkProjections___lam__2___closed__0;
    v___x_5491_ = l_Lean_stringToMessageData(v___x_5490_);
    return v___x_5491_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___lam__2___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5493_ = l_Lean_Meta_mkProjections___lam__2___closed__2;
    v___x_5494_ = l_Lean_stringToMessageData(v___x_5493_);
    return v___x_5494_;
}
pub unsafe fn l_Lean_Meta_mkProjections___lam__2(
    mut v_n_5495_: *mut crate::leanh::LeanObject,
    mut v___x_5496_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5497_: u8,
    mut v_projDecls_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5533_: u8 = 0;
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5537_: u8 = 0;
    let mut v_a_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5541_: u8 = 0;
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: u8 = 0;
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5558_: u8 = 0;
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_n_5495_);
                v___x_5504_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkProjections_spec__0(
                    v_n_5495_,
                    v___y_5499_,
                    v___y_5500_,
                    v___y_5501_,
                    v___y_5502_,
                );
                if crate::leanh::lean_obj_tag(v___x_5504_) == 0 {
                    v_a_5505_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                    crate::leanh::lean_inc(v_a_5505_);
                    crate::leanh::lean_dec_ref_known(v___x_5504_, 1);
                    v___x_5546_ = l_Lean_InductiveVal_numCtors(v_a_5505_);
                    v___x_5547_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5548_ = lean_nat_dec_eq(v___x_5546_, v___x_5547_);
                    crate::leanh::lean_dec(v___x_5546_);
                    if v___x_5548_ == 0 {
                        crate::leanh::lean_dec(v_a_5505_);
                        crate::leanh::lean_dec_ref(v_projDecls_5498_);
                        v___x_5549_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___lam__2___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkProjections___lam__2___closed__1_once
                            ),
                            _init_l_Lean_Meta_mkProjections___lam__2___closed__1,
                        );
                        v___x_5550_ = l_Lean_MessageData_ofConstName(v_n_5495_, v___x_5548_);
                        v___x_5551_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5551_, 0, v___x_5549_);
                        crate::leanh::lean_ctor_set(v___x_5551_, 1, v___x_5550_);
                        v___x_5552_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___lam__2___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_mkProjections___lam__2___closed__3_once
                            ),
                            _init_l_Lean_Meta_mkProjections___lam__2___closed__3,
                        );
                        v___x_5553_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5553_, 0, v___x_5551_);
                        crate::leanh::lean_ctor_set(v___x_5553_, 1, v___x_5552_);
                        v___x_5554_ =
                            l_Lean_throwError___at___00Lean_Meta_getStructureName_spec__0___redArg(
                                v___x_5553_,
                                v___y_5499_,
                                v___y_5500_,
                                v___y_5501_,
                                v___y_5502_,
                            );
                        return v___x_5554_;
                    } else {
                        v___y_5507_ = v___y_5499_;
                        v___y_5508_ = v___y_5500_;
                        v___y_5509_ = v___y_5501_;
                        v___y_5510_ = v___y_5502_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_projDecls_5498_);
                    crate::leanh::lean_dec(v_n_5495_);
                    v_a_5555_ = crate::leanh::lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5562_ = (!crate::leanh::lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5562_ == 0 {
                        v___x_5557_ = v___x_5504_;
                        v_isShared_5558_ = v_isSharedCheck_5562_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5555_);
                        crate::leanh::lean_dec(v___x_5504_);
                        v___x_5557_ = crate::leanh::lean_box(0);
                        v_isShared_5558_ = v_isSharedCheck_5562_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_toConstantVal_5511_ = crate::leanh::lean_ctor_get(v_a_5505_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_5511_);
                v_numParams_5512_ = crate::leanh::lean_ctor_get(v_a_5505_, 1);
                crate::leanh::lean_inc(v_numParams_5512_);
                v_ctors_5513_ = crate::leanh::lean_ctor_get(v_a_5505_, 4);
                crate::leanh::lean_inc(v_ctors_5513_);
                crate::leanh::lean_dec(v_a_5505_);
                v___x_5514_ = l_List_head_x21___redArg(v___x_5496_, v_ctors_5513_);
                crate::leanh::lean_dec(v_ctors_5513_);
                v___x_5515_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1(
                    v___x_5514_,
                    v___y_5507_,
                    v___y_5508_,
                    v___y_5509_,
                    v___y_5510_,
                );
                if crate::leanh::lean_obj_tag(v___x_5515_) == 0 {
                    v_a_5516_ = crate::leanh::lean_ctor_get(v___x_5515_, 0);
                    crate::leanh::lean_inc(v_a_5516_);
                    crate::leanh::lean_dec_ref_known(v___x_5515_, 1);
                    v_levelParams_5517_ = crate::leanh::lean_ctor_get(v_toConstantVal_5511_, 1);
                    crate::leanh::lean_inc(v_levelParams_5517_);
                    v_type_5518_ = crate::leanh::lean_ctor_get(v_toConstantVal_5511_, 2);
                    crate::leanh::lean_inc_ref(v_type_5518_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_5511_);
                    v___x_5519_ = l_Lean_Meta_isPropFormerType(
                        v_type_5518_,
                        v___y_5507_,
                        v___y_5508_,
                        v___y_5509_,
                        v___y_5510_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5519_) == 0 {
                        v_toConstantVal_5520_ = crate::leanh::lean_ctor_get(v_a_5516_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_5520_);
                        crate::leanh::lean_dec(v_a_5516_);
                        v_a_5521_ = crate::leanh::lean_ctor_get(v___x_5519_, 0);
                        crate::leanh::lean_inc(v_a_5521_);
                        crate::leanh::lean_dec_ref_known(v___x_5519_, 1);
                        v_type_5522_ = crate::leanh::lean_ctor_get(v_toConstantVal_5520_, 2);
                        crate::leanh::lean_inc_ref(v_type_5522_);
                        v___x_5523_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_levelParams_5517_);
                        v___x_5524_ = l_List_mapTR_loop___at___00Lean_Meta_mkProjections_spec__2(
                            v_levelParams_5517_,
                            v___x_5523_,
                        );
                        v___x_5525_ = crate::leanh::lean_box((v_instImplicit_5497_) as usize);
                        crate::leanh::lean_inc(v_numParams_5512_);
                        v___f_5526_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_mkProjections___lam__1___boxed as *mut core::ffi::c_void,
                            15,
                            8,
                        );
                        crate::leanh::lean_closure_set(v___f_5526_, 0, v___x_5525_);
                        crate::leanh::lean_closure_set(v___f_5526_, 1, v_projDecls_5498_);
                        crate::leanh::lean_closure_set(v___f_5526_, 2, v_toConstantVal_5520_);
                        crate::leanh::lean_closure_set(v___f_5526_, 3, v_numParams_5512_);
                        crate::leanh::lean_closure_set(v___f_5526_, 4, v___x_5524_);
                        crate::leanh::lean_closure_set(v___f_5526_, 5, v_n_5495_);
                        crate::leanh::lean_closure_set(v___f_5526_, 6, v_levelParams_5517_);
                        crate::leanh::lean_closure_set(v___f_5526_, 7, v_a_5521_);
                        v___x_5527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5527_, 0, v_numParams_5512_);
                        v___x_5528_ = 0;
                        v___x_5529_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_mkProjections_spec__10___redArg(v_type_5522_, v___x_5527_, v___f_5526_, v___x_5528_, v___x_5528_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_);
                        return v___x_5529_;
                    } else {
                        crate::leanh::lean_dec(v_levelParams_5517_);
                        crate::leanh::lean_dec(v_a_5516_);
                        crate::leanh::lean_dec(v_numParams_5512_);
                        crate::leanh::lean_dec_ref(v_projDecls_5498_);
                        crate::leanh::lean_dec(v_n_5495_);
                        v_a_5530_ = crate::leanh::lean_ctor_get(v___x_5519_, 0);
                        v_isSharedCheck_5537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5519_)) as u8;
                        if v_isSharedCheck_5537_ == 0 {
                            v___x_5532_ = v___x_5519_;
                            v_isShared_5533_ = v_isSharedCheck_5537_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5530_);
                            crate::leanh::lean_dec(v___x_5519_);
                            v___x_5532_ = crate::leanh::lean_box(0);
                            v_isShared_5533_ = v_isSharedCheck_5537_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_numParams_5512_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_5511_);
                    crate::leanh::lean_dec_ref(v_projDecls_5498_);
                    crate::leanh::lean_dec(v_n_5495_);
                    v_a_5538_ = crate::leanh::lean_ctor_get(v___x_5515_, 0);
                    v_isSharedCheck_5545_ = (!crate::leanh::lean_is_exclusive(v___x_5515_)) as u8;
                    if v_isSharedCheck_5545_ == 0 {
                        v___x_5540_ = v___x_5515_;
                        v_isShared_5541_ = v_isSharedCheck_5545_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5538_);
                        crate::leanh::lean_dec(v___x_5515_);
                        v___x_5540_ = crate::leanh::lean_box(0);
                        v_isShared_5541_ = v_isSharedCheck_5545_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5533_ == 0 {
                    v___x_5535_ = v___x_5532_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
                    v___x_5535_ = v_reuseFailAlloc_5536_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5535_;
            }
            4 => {
                if v_isShared_5541_ == 0 {
                    v___x_5543_ = v___x_5540_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
                    v___x_5543_ = v_reuseFailAlloc_5544_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5543_;
            }
            6 => {
                if v_isShared_5558_ == 0 {
                    v___x_5560_ = v___x_5557_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
                    v___x_5560_ = v_reuseFailAlloc_5561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkProjections___lam__2___boxed(
    mut v_n_5563_: *mut crate::leanh::LeanObject,
    mut v___x_5564_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5565_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_instImplicit_boxed_5572_: u8 = 0;
    let mut v_res_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5572_ = (crate::leanh::lean_unbox(v_instImplicit_5565_) as u8);
    v_res_5573_ = l_Lean_Meta_mkProjections___lam__2(
        v_n_5563_,
        v___x_5564_,
        v_instImplicit_boxed_5572_,
        v_projDecls_5566_,
        v___y_5567_,
        v___y_5568_,
        v___y_5569_,
        v___y_5570_,
    );
    crate::leanh::lean_dec(v___y_5570_);
    crate::leanh::lean_dec_ref(v___y_5569_);
    crate::leanh::lean_dec(v___y_5568_);
    crate::leanh::lean_dec_ref(v___y_5567_);
    crate::leanh::lean_dec(v___x_5564_);
    return v_res_5573_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5574_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5575_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__0_once),
        _init_l_Lean_Meta_mkProjections___closed__0,
    );
    v___x_5576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5576_, 0, v___x_5575_);
    return v___x_5576_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5577_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5578_ = lean_mk_empty_array_with_capacity(v___x_5577_);
    v___x_5579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5579_, 0, v___x_5578_);
    return v___x_5579_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5580_: usize = 0;
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5580_ = 5usize;
    v___x_5581_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5582_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5583_ = lean_mk_empty_array_with_capacity(v___x_5582_);
    v___x_5584_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__2_once),
        _init_l_Lean_Meta_mkProjections___closed__2,
    );
    v___x_5585_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5585_, 0, v___x_5584_);
    crate::leanh::lean_ctor_set(v___x_5585_, 1, v___x_5583_);
    crate::leanh::lean_ctor_set(v___x_5585_, 2, v___x_5581_);
    crate::leanh::lean_ctor_set(v___x_5585_, 3, v___x_5581_);
    crate::leanh::lean_ctor_set_usize(v___x_5585_, 4, v___x_5580_);
    return v___x_5585_;
}
pub unsafe fn _init_l_Lean_Meta_mkProjections___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5586_ = crate::leanh::lean_box(1);
    v___x_5587_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__3_once),
        _init_l_Lean_Meta_mkProjections___closed__3,
    );
    v___x_5588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__1_once),
        _init_l_Lean_Meta_mkProjections___closed__1,
    );
    v___x_5589_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5589_, 0, v___x_5588_);
    crate::leanh::lean_ctor_set(v___x_5589_, 1, v___x_5587_);
    crate::leanh::lean_ctor_set(v___x_5589_, 2, v___x_5586_);
    return v___x_5589_;
}
pub unsafe fn l_Lean_Meta_mkProjections(
    mut v_n_5592_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5593_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5594_: u8,
    mut v_a_5595_: *mut crate::leanh::LeanObject,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
    mut v_a_5598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5600_ = crate::leanh::lean_box(0);
    v___x_5601_ = crate::leanh::lean_box((v_instImplicit_5594_) as usize);
    v___f_5602_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_mkProjections___lam__2___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_5602_, 0, v_n_5592_);
    crate::leanh::lean_closure_set(v___f_5602_, 1, v___x_5600_);
    crate::leanh::lean_closure_set(v___f_5602_, 2, v___x_5601_);
    crate::leanh::lean_closure_set(v___f_5602_, 3, v_projDecls_5593_);
    v___x_5603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkProjections___closed__4_once),
        _init_l_Lean_Meta_mkProjections___closed__4,
    );
    v___x_5604_ = l_Lean_Meta_mkProjections___closed__5;
    v___x_5605_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_mkProjections_spec__11___redArg(
        v___x_5603_,
        v___x_5604_,
        v___f_5602_,
        v_a_5595_,
        v_a_5596_,
        v_a_5597_,
        v_a_5598_,
    );
    return v___x_5605_;
}
pub unsafe fn l_Lean_Meta_mkProjections___boxed(
    mut v_n_5606_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5607_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5608_: *mut crate::leanh::LeanObject,
    mut v_a_5609_: *mut crate::leanh::LeanObject,
    mut v_a_5610_: *mut crate::leanh::LeanObject,
    mut v_a_5611_: *mut crate::leanh::LeanObject,
    mut v_a_5612_: *mut crate::leanh::LeanObject,
    mut v_a_5613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_instImplicit_boxed_5614_: u8 = 0;
    let mut v_res_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5614_ = (crate::leanh::lean_unbox(v_instImplicit_5608_) as u8);
    v_res_5615_ = l_Lean_Meta_mkProjections(
        v_n_5606_,
        v_projDecls_5607_,
        v_instImplicit_boxed_5614_,
        v_a_5609_,
        v_a_5610_,
        v_a_5611_,
        v_a_5612_,
    );
    crate::leanh::lean_dec(v_a_5612_);
    crate::leanh::lean_dec_ref(v_a_5611_);
    crate::leanh::lean_dec(v_a_5610_);
    crate::leanh::lean_dec_ref(v_a_5609_);
    return v_res_5615_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(
    mut v_instImplicit_5616_: u8,
    mut v_as_5617_: *mut crate::leanh::LeanObject,
    mut v_sz_5618_: usize,
    mut v_i_5619_: usize,
    mut v_b_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___redArg(v_instImplicit_5616_, v_as_5617_, v_sz_5618_, v_i_5619_, v_b_5620_, v___y_5621_, v___y_5623_, v___y_5624_);
    return v___x_5626_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3___boxed(
    mut v_instImplicit_5627_: *mut crate::leanh::LeanObject,
    mut v_as_5628_: *mut crate::leanh::LeanObject,
    mut v_sz_5629_: *mut crate::leanh::LeanObject,
    mut v_i_5630_: *mut crate::leanh::LeanObject,
    mut v_b_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
    mut v___y_5634_: *mut crate::leanh::LeanObject,
    mut v___y_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_instImplicit_boxed_5637_: u8 = 0;
    let mut v_sz_boxed_5638_: usize = 0;
    let mut v_i_boxed_5639_: usize = 0;
    let mut v_res_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5637_ = (crate::leanh::lean_unbox(v_instImplicit_5627_) as u8);
    v_sz_boxed_5638_ = crate::leanh::lean_unbox_usize(v_sz_5629_);
    crate::leanh::lean_dec(v_sz_5629_);
    v_i_boxed_5639_ = crate::leanh::lean_unbox_usize(v_i_5630_);
    crate::leanh::lean_dec(v_i_5630_);
    v_res_5640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjections_spec__3(v_instImplicit_boxed_5637_, v_as_5628_, v_sz_boxed_5638_, v_i_boxed_5639_, v_b_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
    crate::leanh::lean_dec(v___y_5635_);
    crate::leanh::lean_dec_ref(v___y_5634_);
    crate::leanh::lean_dec(v___y_5633_);
    crate::leanh::lean_dec_ref(v___y_5632_);
    crate::leanh::lean_dec_ref(v_as_5628_);
    return v_res_5640_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(
    mut v_declName_5641_: *mut crate::leanh::LeanObject,
    mut v_s_5642_: u8,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5648_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___redArg(v_declName_5641_, v_s_5642_, v___y_5644_, v___y_5646_);
    return v___x_5648_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6___boxed(
    mut v_declName_5649_: *mut crate::leanh::LeanObject,
    mut v_s_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
    mut v___y_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_5656_: u8 = 0;
    let mut v_res_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_5656_ = (crate::leanh::lean_unbox(v_s_5650_) as u8);
    v_res_5657_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkProjections_spec__5_spec__6(v_declName_5649_, v_s_boxed_5656_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_);
    crate::leanh::lean_dec(v___y_5654_);
    crate::leanh::lean_dec_ref(v___y_5653_);
    crate::leanh::lean_dec(v___y_5652_);
    crate::leanh::lean_dec_ref(v___y_5651_);
    return v_res_5657_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(
    mut v_00_u03b1_5658_: *mut crate::leanh::LeanObject,
    mut v_ref_5659_: *mut crate::leanh::LeanObject,
    mut v_msg_5660_: *mut crate::leanh::LeanObject,
    mut v___y_5661_: *mut crate::leanh::LeanObject,
    mut v___y_5662_: *mut crate::leanh::LeanObject,
    mut v___y_5663_: *mut crate::leanh::LeanObject,
    mut v___y_5664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5666_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___redArg(
        v_ref_5659_,
        v_msg_5660_,
        v___y_5661_,
        v___y_5662_,
        v___y_5663_,
        v___y_5664_,
    );
    return v___x_5666_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6___boxed(
    mut v_00_u03b1_5667_: *mut crate::leanh::LeanObject,
    mut v_ref_5668_: *mut crate::leanh::LeanObject,
    mut v_msg_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5675_ = l_Lean_throwErrorAt___at___00Lean_Meta_mkProjections_spec__6(
        v_00_u03b1_5667_,
        v_ref_5668_,
        v_msg_5669_,
        v___y_5670_,
        v___y_5671_,
        v___y_5672_,
        v___y_5673_,
    );
    crate::leanh::lean_dec(v___y_5673_);
    crate::leanh::lean_dec_ref(v___y_5672_);
    crate::leanh::lean_dec(v___y_5671_);
    crate::leanh::lean_dec_ref(v___y_5670_);
    crate::leanh::lean_dec(v_ref_5668_);
    return v_res_5675_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(
    mut v_00_u03b1_5676_: *mut crate::leanh::LeanObject,
    mut v_x_5677_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5678_: u8,
    mut v___y_5679_: *mut crate::leanh::LeanObject,
    mut v___y_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___redArg(v_x_5677_, v_isExporting_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9___boxed(
    mut v_00_u03b1_5685_: *mut crate::leanh::LeanObject,
    mut v_x_5686_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_5693_: u8 = 0;
    let mut v_res_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5693_ = (crate::leanh::lean_unbox(v_isExporting_5687_) as u8);
    v_res_5694_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7_spec__9(v_00_u03b1_5685_, v_x_5686_, v_isExporting_boxed_5693_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
    crate::leanh::lean_dec(v___y_5691_);
    crate::leanh::lean_dec_ref(v___y_5690_);
    crate::leanh::lean_dec(v___y_5689_);
    crate::leanh::lean_dec_ref(v___y_5688_);
    return v_res_5694_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(
    mut v_00_u03b1_5695_: *mut crate::leanh::LeanObject,
    mut v_x_5696_: *mut crate::leanh::LeanObject,
    mut v_when_5697_: u8,
    mut v___y_5698_: *mut crate::leanh::LeanObject,
    mut v___y_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5703_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___redArg(
        v_x_5696_,
        v_when_5697_,
        v___y_5698_,
        v___y_5699_,
        v___y_5700_,
        v___y_5701_,
    );
    return v___x_5703_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7___boxed(
    mut v_00_u03b1_5704_: *mut crate::leanh::LeanObject,
    mut v_x_5705_: *mut crate::leanh::LeanObject,
    mut v_when_5706_: *mut crate::leanh::LeanObject,
    mut v___y_5707_: *mut crate::leanh::LeanObject,
    mut v___y_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
    mut v___y_5710_: *mut crate::leanh::LeanObject,
    mut v___y_5711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_5712_: u8 = 0;
    let mut v_res_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_5712_ = (crate::leanh::lean_unbox(v_when_5706_) as u8);
    v_res_5713_ = l_Lean_withoutExporting___at___00Lean_Meta_mkProjections_spec__7(
        v_00_u03b1_5704_,
        v_x_5705_,
        v_when_boxed_5712_,
        v___y_5707_,
        v___y_5708_,
        v___y_5709_,
        v___y_5710_,
    );
    crate::leanh::lean_dec(v___y_5710_);
    crate::leanh::lean_dec_ref(v___y_5709_);
    crate::leanh::lean_dec(v___y_5708_);
    crate::leanh::lean_dec_ref(v___y_5707_);
    return v_res_5713_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(
    mut v_upperBound_5714_: *mut crate::leanh::LeanObject,
    mut v_projDecls_5715_: *mut crate::leanh::LeanObject,
    mut v___x_5716_: *mut crate::leanh::LeanObject,
    mut v___x_5717_: *mut crate::leanh::LeanObject,
    mut v_instImplicit_5718_: u8,
    mut v___x_5719_: *mut crate::leanh::LeanObject,
    mut v_params_5720_: *mut crate::leanh::LeanObject,
    mut v_self_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v___x_5723_: *mut crate::leanh::LeanObject,
    mut v_n_5724_: *mut crate::leanh::LeanObject,
    mut v___x_5725_: *mut crate::leanh::LeanObject,
    mut v_a_5726_: u8,
    mut v_inst_5727_: *mut crate::leanh::LeanObject,
    mut v_R_5728_: *mut crate::leanh::LeanObject,
    mut v_a_5729_: *mut crate::leanh::LeanObject,
    mut v_b_5730_: *mut crate::leanh::LeanObject,
    mut v_c_5731_: *mut crate::leanh::LeanObject,
    mut v___y_5732_: *mut crate::leanh::LeanObject,
    mut v___y_5733_: *mut crate::leanh::LeanObject,
    mut v___y_5734_: *mut crate::leanh::LeanObject,
    mut v___y_5735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___redArg(
        v_upperBound_5714_,
        v_projDecls_5715_,
        v___x_5716_,
        v___x_5717_,
        v_instImplicit_5718_,
        v___x_5719_,
        v_params_5720_,
        v_self_5721_,
        v_a_5722_,
        v___x_5723_,
        v_n_5724_,
        v___x_5725_,
        v_a_5726_,
        v_a_5729_,
        v_b_5730_,
        v___y_5732_,
        v___y_5733_,
        v___y_5734_,
        v___y_5735_,
    );
    return v___x_5737_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_5738_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_projDecls_5739_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_5740_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5741_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_instImplicit_5742_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5743_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_params_5744_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_self_5745_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_5746_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5747_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_n_5748_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_5749_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_5750_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_inst_5751_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_R_5752_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_5753_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_b_5754_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_c_5755_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5756_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5757_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_5758_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_5759_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_5760_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_instImplicit_boxed_5761_: u8 = 0;
    let mut v_a_20508__boxed_5762_: u8 = 0;
    let mut v_res_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_instImplicit_boxed_5761_ = (crate::leanh::lean_unbox(v_instImplicit_5742_) as u8);
    v_a_20508__boxed_5762_ = (crate::leanh::lean_unbox(v_a_5750_) as u8);
    v_res_5763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProjections_spec__8(
        v_upperBound_5738_,
        v_projDecls_5739_,
        v___x_5740_,
        v___x_5741_,
        v_instImplicit_boxed_5761_,
        v___x_5743_,
        v_params_5744_,
        v_self_5745_,
        v_a_5746_,
        v___x_5747_,
        v_n_5748_,
        v___x_5749_,
        v_a_20508__boxed_5762_,
        v_inst_5751_,
        v_R_5752_,
        v_a_5753_,
        v_b_5754_,
        v_c_5755_,
        v___y_5756_,
        v___y_5757_,
        v___y_5758_,
        v___y_5759_,
    );
    crate::leanh::lean_dec(v___y_5759_);
    crate::leanh::lean_dec_ref(v___y_5758_);
    crate::leanh::lean_dec(v___y_5757_);
    crate::leanh::lean_dec_ref(v___y_5756_);
    crate::leanh::lean_dec_ref(v_projDecls_5739_);
    crate::leanh::lean_dec(v_upperBound_5738_);
    return v_res_5763_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(
    mut v_k_5764_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5765_: u8,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
    mut v___y_5768_: *mut crate::leanh::LeanObject,
    mut v___y_5769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5779_: u8 = 0;
    let mut v_a_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5771_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_5765_,
                    v_k_5764_,
                    v___y_5766_,
                    v___y_5767_,
                    v___y_5768_,
                    v___y_5769_,
                );
                if crate::leanh::lean_obj_tag(v___x_5771_) == 0 {
                    v_a_5772_ = crate::leanh::lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5779_ = (!crate::leanh::lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5779_ == 0 {
                        v___x_5774_ = v___x_5771_;
                        v_isShared_5775_ = v_isSharedCheck_5779_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5772_);
                        crate::leanh::lean_dec(v___x_5771_);
                        v___x_5774_ = crate::leanh::lean_box(0);
                        v_isShared_5775_ = v_isSharedCheck_5779_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5780_ = crate::leanh::lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5787_ = (!crate::leanh::lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5787_ == 0 {
                        v___x_5782_ = v___x_5771_;
                        v_isShared_5783_ = v_isSharedCheck_5787_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5780_);
                        crate::leanh::lean_dec(v___x_5771_);
                        v___x_5782_ = crate::leanh::lean_box(0);
                        v_isShared_5783_ = v_isSharedCheck_5787_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5775_ == 0 {
                    v___x_5777_ = v___x_5774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5772_);
                    v___x_5777_ = v_reuseFailAlloc_5778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5777_;
            }
            3 => {
                if v_isShared_5783_ == 0 {
                    v___x_5785_ = v___x_5782_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5786_, 0, v_a_5780_);
                    v___x_5785_ = v_reuseFailAlloc_5786_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg___boxed(
    mut v_k_5788_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_5795_: u8 = 0;
    let mut v_res_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_5795_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_5789_) as u8);
    v_res_5796_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_5788_, v_allowLevelAssignments_boxed_5795_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
    crate::leanh::lean_dec(v___y_5793_);
    crate::leanh::lean_dec_ref(v___y_5792_);
    crate::leanh::lean_dec(v___y_5791_);
    crate::leanh::lean_dec_ref(v___y_5790_);
    return v_res_5796_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(
    mut v_00_u03b1_5797_: *mut crate::leanh::LeanObject,
    mut v_k_5798_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5799_: u8,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
    mut v___y_5803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5805_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v_k_5798_, v_allowLevelAssignments_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
    return v___x_5805_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___boxed(
    mut v_00_u03b1_5806_: *mut crate::leanh::LeanObject,
    mut v_k_5807_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_5814_: u8 = 0;
    let mut v_res_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_5814_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_5808_) as u8);
    v_res_5815_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1(v_00_u03b1_5806_, v_k_5807_, v_allowLevelAssignments_boxed_5814_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_);
    crate::leanh::lean_dec(v___y_5812_);
    crate::leanh::lean_dec_ref(v___y_5811_);
    crate::leanh::lean_dec(v___y_5810_);
    crate::leanh::lean_dec_ref(v___y_5809_);
    return v_res_5815_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(
    mut v_as_5816_: *mut crate::leanh::LeanObject,
    mut v_sz_5817_: usize,
    mut v_i_5818_: usize,
    mut v_b_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5825_: u8 = 0;
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5830_: u8 = 0;
    let mut v_array_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: u8 = 0;
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5842_: u8 = 0;
    let mut v_a_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5849_: u8 = 0;
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: u8 = 0;
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: usize = 0;
    let mut v___x_5865_: usize = 0;
    let mut v_reuseFailAlloc_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5869_: u8 = 0;
    let mut v_a_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5873_: u8 = 0;
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_isSharedCheck_5878_: u8 = 0;
    let mut v_unused_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut v_unused_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5825_ = lean_usize_dec_lt(v_i_5818_, v_sz_5817_);
                if v___x_5825_ == 0 {
                    v___x_5826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5826_, 0, v_b_5819_);
                    return v___x_5826_;
                } else {
                    v_snd_5827_ = crate::leanh::lean_ctor_get(v_b_5819_, 1);
                    v_isSharedCheck_5882_ = (!crate::leanh::lean_is_exclusive(v_b_5819_)) as u8;
                    if v_isSharedCheck_5882_ == 0 {
                        v_unused_5883_ = crate::leanh::lean_ctor_get(v_b_5819_, 0);
                        crate::leanh::lean_dec(v_unused_5883_);
                        v___x_5829_ = v_b_5819_;
                        v_isShared_5830_ = v_isSharedCheck_5882_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5827_);
                        crate::leanh::lean_dec(v_b_5819_);
                        v___x_5829_ = crate::leanh::lean_box(0);
                        v_isShared_5830_ = v_isSharedCheck_5882_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_5831_ = crate::leanh::lean_ctor_get(v_snd_5827_, 0);
                v_start_5832_ = crate::leanh::lean_ctor_get(v_snd_5827_, 1);
                v_stop_5833_ = crate::leanh::lean_ctor_get(v_snd_5827_, 2);
                v___x_5834_ = crate::leanh::lean_box(0);
                v___x_5835_ = lean_nat_dec_lt(v_start_5832_, v_stop_5833_);
                if v___x_5835_ == 0 {
                    if v_isShared_5830_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5829_, 0, v___x_5834_);
                        v___x_5837_ = v___x_5829_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5839_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5839_, 0, v___x_5834_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5839_, 1, v_snd_5827_);
                        v___x_5837_ = v_reuseFailAlloc_5839_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_5833_);
                    crate::leanh::lean_inc(v_start_5832_);
                    crate::leanh::lean_inc_ref(v_array_5831_);
                    v_isSharedCheck_5878_ = (!crate::leanh::lean_is_exclusive(v_snd_5827_)) as u8;
                    if v_isSharedCheck_5878_ == 0 {
                        v_unused_5879_ = crate::leanh::lean_ctor_get(v_snd_5827_, 2);
                        crate::leanh::lean_dec(v_unused_5879_);
                        v_unused_5880_ = crate::leanh::lean_ctor_get(v_snd_5827_, 1);
                        crate::leanh::lean_dec(v_unused_5880_);
                        v_unused_5881_ = crate::leanh::lean_ctor_get(v_snd_5827_, 0);
                        crate::leanh::lean_dec(v_unused_5881_);
                        v___x_5841_ = v_snd_5827_;
                        v_isShared_5842_ = v_isSharedCheck_5878_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_5827_);
                        v___x_5841_ = crate::leanh::lean_box(0);
                        v_isShared_5842_ = v_isSharedCheck_5878_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5838_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5838_, 0, v___x_5837_);
                return v___x_5838_;
            }
            3 => {
                v_a_5843_ = lean_array_uget_borrowed(v_as_5816_, v_i_5818_);
                v___x_5844_ = lean_array_fget_borrowed(v_array_5831_, v_start_5832_);
                crate::leanh::lean_inc(v___x_5844_);
                crate::leanh::lean_inc(v_a_5843_);
                v___x_5845_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_a_5843_,
                    v___x_5844_,
                    v___y_5820_,
                    v___y_5821_,
                    v___y_5822_,
                    v___y_5823_,
                );
                if crate::leanh::lean_obj_tag(v___x_5845_) == 0 {
                    v_a_5846_ = crate::leanh::lean_ctor_get(v___x_5845_, 0);
                    v_isSharedCheck_5869_ = (!crate::leanh::lean_is_exclusive(v___x_5845_)) as u8;
                    if v_isSharedCheck_5869_ == 0 {
                        v___x_5848_ = v___x_5845_;
                        v_isShared_5849_ = v_isSharedCheck_5869_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5846_);
                        crate::leanh::lean_dec(v___x_5845_);
                        v___x_5848_ = crate::leanh::lean_box(0);
                        v_isShared_5849_ = v_isSharedCheck_5869_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5841_);
                    crate::leanh::lean_dec(v_stop_5833_);
                    crate::leanh::lean_dec(v_start_5832_);
                    crate::leanh::lean_dec_ref(v_array_5831_);
                    crate::leanh::lean_del_object(v___x_5829_);
                    v_a_5870_ = crate::leanh::lean_ctor_get(v___x_5845_, 0);
                    v_isSharedCheck_5877_ = (!crate::leanh::lean_is_exclusive(v___x_5845_)) as u8;
                    if v_isSharedCheck_5877_ == 0 {
                        v___x_5872_ = v___x_5845_;
                        v_isShared_5873_ = v_isSharedCheck_5877_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5870_);
                        crate::leanh::lean_dec(v___x_5845_);
                        v___x_5872_ = crate::leanh::lean_box(0);
                        v_isShared_5873_ = v_isSharedCheck_5877_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5850_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5851_ = lean_nat_add(v_start_5832_, v___x_5850_);
                crate::leanh::lean_dec(v_start_5832_);
                if v_isShared_5842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5841_, 1, v___x_5851_);
                    v___x_5853_ = v___x_5841_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5868_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_array_5831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 1, v___x_5851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_stop_5833_);
                    v___x_5853_ = v_reuseFailAlloc_5868_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5854_ = (crate::leanh::lean_unbox(v_a_5846_) as u8);
                if v___x_5854_ == 0 {
                    v___x_5855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5855_, 0, v_a_5846_);
                    if v_isShared_5830_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5829_, 1, v___x_5853_);
                        crate::leanh::lean_ctor_set(v___x_5829_, 0, v___x_5855_);
                        v___x_5857_ = v___x_5829_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5861_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5861_, 0, v___x_5855_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5861_, 1, v___x_5853_);
                        v___x_5857_ = v_reuseFailAlloc_5861_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5848_);
                    crate::leanh::lean_dec(v_a_5846_);
                    if v_isShared_5830_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5829_, 1, v___x_5853_);
                        crate::leanh::lean_ctor_set(v___x_5829_, 0, v___x_5834_);
                        v___x_5863_ = v___x_5829_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5867_, 0, v___x_5834_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5867_, 1, v___x_5853_);
                        v___x_5863_ = v_reuseFailAlloc_5867_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5849_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5848_, 0, v___x_5857_);
                    v___x_5859_ = v___x_5848_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5860_, 0, v___x_5857_);
                    v___x_5859_ = v_reuseFailAlloc_5860_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5859_;
            }
            8 => {
                v___x_5864_ = 1usize;
                v___x_5865_ = lean_usize_add(v_i_5818_, v___x_5864_);
                v_i_5818_ = v___x_5865_;
                v_b_5819_ = v___x_5863_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_5873_ == 0 {
                    v___x_5875_ = v___x_5872_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
                    v___x_5875_ = v_reuseFailAlloc_5876_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0___boxed(
    mut v_as_5884_: *mut crate::leanh::LeanObject,
    mut v_sz_5885_: *mut crate::leanh::LeanObject,
    mut v_i_5886_: *mut crate::leanh::LeanObject,
    mut v_b_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
    mut v___y_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5893_: usize = 0;
    let mut v_i_boxed_5894_: usize = 0;
    let mut v_res_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5893_ = crate::leanh::lean_unbox_usize(v_sz_5885_);
    crate::leanh::lean_dec(v_sz_5885_);
    v_i_boxed_5894_ = crate::leanh::lean_unbox_usize(v_i_5886_);
    crate::leanh::lean_dec(v_i_5886_);
    v_res_5895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_as_5884_, v_sz_boxed_5893_, v_i_boxed_5894_, v_b_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
    crate::leanh::lean_dec(v___y_5891_);
    crate::leanh::lean_dec_ref(v___y_5890_);
    crate::leanh::lean_dec(v___y_5889_);
    crate::leanh::lean_dec_ref(v___y_5888_);
    crate::leanh::lean_dec_ref(v_as_5884_);
    return v_res_5895_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(
    mut v___x_5896_: u8,
    mut v_params2_5897_: *mut crate::leanh::LeanObject,
    mut v___x_5898_: *mut crate::leanh::LeanObject,
    mut v_params1_5899_: *mut crate::leanh::LeanObject,
    mut v___x_5900_: u8,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
    mut v___y_5903_: *mut crate::leanh::LeanObject,
    mut v___y_5904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5912_: usize = 0;
    let mut v___x_5913_: usize = 0;
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5918_: u8 = 0;
    let mut v_fst_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut v_a_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5932_: u8 = 0;
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_5896_ == 0 {
                    crate::leanh::lean_dec(v___x_5898_);
                    crate::leanh::lean_dec_ref(v_params2_5897_);
                    v___x_5906_ = crate::leanh::lean_box((v___x_5896_) as usize);
                    v___x_5907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5907_, 0, v___x_5906_);
                    return v___x_5907_;
                } else {
                    v___x_5908_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5909_ =
                        l_Array_toSubarray___redArg(v_params2_5897_, v___x_5908_, v___x_5898_);
                    v___x_5910_ = crate::leanh::lean_box(0);
                    v___x_5911_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5911_, 0, v___x_5910_);
                    crate::leanh::lean_ctor_set(v___x_5911_, 1, v___x_5909_);
                    v_sz_5912_ = lean_array_size(v_params1_5899_);
                    v___x_5913_ = 0usize;
                    v___x_5914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__0(v_params1_5899_, v_sz_5912_, v___x_5913_, v___x_5911_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_);
                    if crate::leanh::lean_obj_tag(v___x_5914_) == 0 {
                        v_a_5915_ = crate::leanh::lean_ctor_get(v___x_5914_, 0);
                        v_isSharedCheck_5928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5914_)) as u8;
                        if v_isSharedCheck_5928_ == 0 {
                            v___x_5917_ = v___x_5914_;
                            v_isShared_5918_ = v_isSharedCheck_5928_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5915_);
                            crate::leanh::lean_dec(v___x_5914_);
                            v___x_5917_ = crate::leanh::lean_box(0);
                            v_isShared_5918_ = v_isSharedCheck_5928_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5929_ = crate::leanh::lean_ctor_get(v___x_5914_, 0);
                        v_isSharedCheck_5936_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5914_)) as u8;
                        if v_isSharedCheck_5936_ == 0 {
                            v___x_5931_ = v___x_5914_;
                            v_isShared_5932_ = v_isSharedCheck_5936_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5929_);
                            crate::leanh::lean_dec(v___x_5914_);
                            v___x_5931_ = crate::leanh::lean_box(0);
                            v_isShared_5932_ = v_isSharedCheck_5936_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5919_ = crate::leanh::lean_ctor_get(v_a_5915_, 0);
                crate::leanh::lean_inc(v_fst_5919_);
                crate::leanh::lean_dec(v_a_5915_);
                if crate::leanh::lean_obj_tag(v_fst_5919_) == 0 {
                    v___x_5920_ = crate::leanh::lean_box((v___x_5900_) as usize);
                    if v_isShared_5918_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5917_, 0, v___x_5920_);
                        v___x_5922_ = v___x_5917_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 0, v___x_5920_);
                        v___x_5922_ = v_reuseFailAlloc_5923_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5924_ = crate::leanh::lean_ctor_get(v_fst_5919_, 0);
                    crate::leanh::lean_inc(v_val_5924_);
                    crate::leanh::lean_dec_ref_known(v_fst_5919_, 1);
                    if v_isShared_5918_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5917_, 0, v_val_5924_);
                        v___x_5926_ = v___x_5917_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_val_5924_);
                        v___x_5926_ = v_reuseFailAlloc_5927_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5922_;
            }
            3 => {
                return v___x_5926_;
            }
            4 => {
                if v_isShared_5932_ == 0 {
                    v___x_5934_ = v___x_5931_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_a_5929_);
                    v___x_5934_ = v_reuseFailAlloc_5935_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed(
    mut v___x_5937_: *mut crate::leanh::LeanObject,
    mut v_params2_5938_: *mut crate::leanh::LeanObject,
    mut v___x_5939_: *mut crate::leanh::LeanObject,
    mut v_params1_5940_: *mut crate::leanh::LeanObject,
    mut v___x_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
    mut v___y_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2097__boxed_5947_: u8 = 0;
    let mut v___x_2099__boxed_5948_: u8 = 0;
    let mut v_res_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2097__boxed_5947_ = (crate::leanh::lean_unbox(v___x_5937_) as u8);
    v___x_2099__boxed_5948_ = (crate::leanh::lean_unbox(v___x_5941_) as u8);
    v_res_5949_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0(
        v___x_2097__boxed_5947_,
        v_params2_5938_,
        v___x_5939_,
        v_params1_5940_,
        v___x_2099__boxed_5948_,
        v___y_5942_,
        v___y_5943_,
        v___y_5944_,
        v___y_5945_,
    );
    crate::leanh::lean_dec(v___y_5945_);
    crate::leanh::lean_dec_ref(v___y_5944_);
    crate::leanh::lean_dec(v___y_5943_);
    crate::leanh::lean_dec_ref(v___y_5942_);
    crate::leanh::lean_dec_ref(v_params1_5940_);
    return v_res_5949_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(
    mut v_params1_5950_: *mut crate::leanh::LeanObject,
    mut v_params2_5951_: *mut crate::leanh::LeanObject,
    mut v_a_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
    mut v_a_5954_: *mut crate::leanh::LeanObject,
    mut v_a_5955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v___x_5960_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: u8 = 0;
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5957_ = lean_array_get_size(v_params1_5950_);
    v___x_5958_ = lean_array_get_size(v_params2_5951_);
    v___x_5959_ = lean_nat_dec_eq(v___x_5957_, v___x_5958_);
    v___x_5960_ = 1;
    v___x_5961_ = crate::leanh::lean_box((v___x_5959_) as usize);
    v___x_5962_ = crate::leanh::lean_box((v___x_5960_) as usize);
    v___y_5963_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___y_5963_, 0, v___x_5961_);
    crate::leanh::lean_closure_set(v___y_5963_, 1, v_params2_5951_);
    crate::leanh::lean_closure_set(v___y_5963_, 2, v___x_5958_);
    crate::leanh::lean_closure_set(v___y_5963_, 3, v_params1_5950_);
    crate::leanh::lean_closure_set(v___y_5963_, 4, v___x_5962_);
    v___x_5964_ = 0;
    v___x_5965_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams_spec__1___redArg(v___y_5963_, v___x_5964_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
    return v___x_5965_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams___boxed(
    mut v_params1_5966_: *mut crate::leanh::LeanObject,
    mut v_params2_5967_: *mut crate::leanh::LeanObject,
    mut v_a_5968_: *mut crate::leanh::LeanObject,
    mut v_a_5969_: *mut crate::leanh::LeanObject,
    mut v_a_5970_: *mut crate::leanh::LeanObject,
    mut v_a_5971_: *mut crate::leanh::LeanObject,
    mut v_a_5972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5973_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(
        v_params1_5966_,
        v_params2_5967_,
        v_a_5968_,
        v_a_5969_,
        v_a_5970_,
        v_a_5971_,
    );
    crate::leanh::lean_dec(v_a_5971_);
    crate::leanh::lean_dec_ref(v_a_5970_);
    crate::leanh::lean_dec(v_a_5969_);
    crate::leanh::lean_dec_ref(v_a_5968_);
    return v_res_5973_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(
    mut v_declName_5974_: *mut crate::leanh::LeanObject,
    mut v___y_5975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5977_ = lean_st_ref_get(v___y_5975_);
    v_env_5978_ = crate::leanh::lean_ctor_get(v___x_5977_, 0);
    crate::leanh::lean_inc_ref(v_env_5978_);
    crate::leanh::lean_dec(v___x_5977_);
    v___x_5979_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_5978_, v_declName_5974_);
    v___x_5980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5980_, 0, v___x_5979_);
    return v___x_5980_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg___boxed(
    mut v_declName_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5984_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_5981_, v___y_5982_);
    crate::leanh::lean_dec(v___y_5982_);
    return v_res_5984_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(
    mut v_declName_5985_: *mut crate::leanh::LeanObject,
    mut v___y_5986_: *mut crate::leanh::LeanObject,
    mut v___y_5987_: *mut crate::leanh::LeanObject,
    mut v___y_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5991_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_5985_, v___y_5989_);
    return v___x_5991_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___boxed(
    mut v_declName_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5998_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0(v_declName_5992_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
    crate::leanh::lean_dec(v___y_5996_);
    crate::leanh::lean_dec_ref(v___y_5995_);
    crate::leanh::lean_dec(v___y_5994_);
    crate::leanh::lean_dec_ref(v___y_5993_);
    return v_res_5998_;
}
pub unsafe fn _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5999_ = crate::leanh::lean_box(0);
    v_dummy_6000_ = l_Lean_Expr_sort___override(v___x_5999_);
    return v_dummy_6000_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(
    mut v_ctor_6001_: *mut crate::leanh::LeanObject,
    mut v_induct_6002_: *mut crate::leanh::LeanObject,
    mut v_params_6003_: *mut crate::leanh::LeanObject,
    mut v_idx_6004_: *mut crate::leanh::LeanObject,
    mut v_e_6005_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_6006_: *mut crate::leanh::LeanObject,
    mut v_a_6007_: *mut crate::leanh::LeanObject,
    mut v_a_6008_: *mut crate::leanh::LeanObject,
    mut v_a_6009_: *mut crate::leanh::LeanObject,
    mut v_a_6010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v___x_6037_: u8 = 0;
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6042_: u8 = 0;
    let mut v_a_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6046_: u8 = 0;
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6050_: u8 = 0;
    let mut v_a_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v_a_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6062_: u8 = 0;
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6066_: u8 = 0;
    let mut v___y_6068_: u8 = 0;
    let mut v_val_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: u8 = 0;
    let mut v___x_6071_: u8 = 0;
    let mut v___x_6072_: u8 = 0;
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6079_: u8 = 0;
    let mut v___y_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6093_: u8 = 0;
    let mut v___x_6094_: u8 = 0;
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6101_: u8 = 0;
    let mut v_a_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6105_: u8 = 0;
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v_val_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6115_: u8 = 0;
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: u8 = 0;
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: u8 = 0;
    let mut v___x_6123_: u8 = 0;
    let mut v___x_6124_: u8 = 0;
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_6005_) == 11 {
                    v_typeName_6018_ = crate::leanh::lean_ctor_get(v_e_6005_, 0);
                    v_idx_6019_ = crate::leanh::lean_ctor_get(v_e_6005_, 1);
                    v_struct_6020_ = crate::leanh::lean_ctor_get(v_e_6005_, 2);
                    crate::leanh::lean_inc_ref(v_struct_6020_);
                    v___x_6071_ = lean_nat_dec_eq(v_idx_6019_, v_idx_6004_);
                    if v___x_6071_ == 0 {
                        v___y_6068_ = v___x_6071_;
                        state = 12;
                        continue;
                    } else {
                        v___x_6072_ = lean_name_eq(v_induct_6002_, v_typeName_6018_);
                        v___y_6068_ = v___x_6072_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_6073_ = l_Lean_Expr_getAppFn(v_e_6005_);
                    if crate::leanh::lean_obj_tag(v___x_6073_) == 4 {
                        v_declName_6074_ = crate::leanh::lean_ctor_get(v___x_6073_, 0);
                        crate::leanh::lean_inc(v_declName_6074_);
                        crate::leanh::lean_dec_ref_known(v___x_6073_, 2);
                        v___x_6075_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr_spec__0___redArg(v_declName_6074_, v_a_6010_);
                        v_a_6076_ = crate::leanh::lean_ctor_get(v___x_6075_, 0);
                        v_isSharedCheck_6125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6075_)) as u8;
                        if v_isSharedCheck_6125_ == 0 {
                            v___x_6078_ = v___x_6075_;
                            v_isShared_6079_ = v_isSharedCheck_6125_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6076_);
                            crate::leanh::lean_dec(v___x_6075_);
                            v___x_6078_ = crate::leanh::lean_box(0);
                            v_isShared_6079_ = v_isSharedCheck_6125_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6073_);
                        crate::leanh::lean_dec_ref(v_e_6005_);
                        crate::leanh::lean_dec_ref(v_params_6003_);
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6013_ = crate::leanh::lean_box(0);
                v___x_6014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6014_, 0, v___x_6013_);
                return v___x_6014_;
            }
            2 => {
                v___x_6016_ = crate::leanh::lean_box(0);
                v___x_6017_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6017_, 0, v___x_6016_);
                return v___x_6017_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_6010_);
                crate::leanh::lean_inc_ref(v_a_6009_);
                crate::leanh::lean_inc(v_a_6008_);
                crate::leanh::lean_inc_ref(v_a_6007_);
                v___x_6022_ =
                    lean_infer_type(v_e_6005_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
                if crate::leanh::lean_obj_tag(v___x_6022_) == 0 {
                    v_a_6023_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                    crate::leanh::lean_inc(v_a_6023_);
                    crate::leanh::lean_dec_ref_known(v___x_6022_, 1);
                    crate::leanh::lean_inc(v_a_6010_);
                    crate::leanh::lean_inc_ref(v_a_6009_);
                    crate::leanh::lean_inc(v_a_6008_);
                    crate::leanh::lean_inc_ref(v_a_6007_);
                    v___x_6024_ = lean_whnf(v_a_6023_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
                    if crate::leanh::lean_obj_tag(v___x_6024_) == 0 {
                        v_a_6025_ = crate::leanh::lean_ctor_get(v___x_6024_, 0);
                        crate::leanh::lean_inc(v_a_6025_);
                        crate::leanh::lean_dec_ref_known(v___x_6024_, 1);
                        v_dummy_6026_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once), _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
                        v_nargs_6027_ = l_Lean_Expr_getAppNumArgs(v_a_6025_);
                        crate::leanh::lean_inc(v_nargs_6027_);
                        v___x_6028_ = lean_mk_array(v_nargs_6027_, v_dummy_6026_);
                        v___x_6029_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6030_ = lean_nat_sub(v_nargs_6027_, v___x_6029_);
                        crate::leanh::lean_dec(v_nargs_6027_);
                        v___x_6031_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_a_6025_,
                            v___x_6028_,
                            v___x_6030_,
                        );
                        v___x_6032_ =
                            l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(
                                v_params_6003_,
                                v___x_6031_,
                                v_a_6007_,
                                v_a_6008_,
                                v_a_6009_,
                                v_a_6010_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6032_) == 0 {
                            v_a_6033_ = crate::leanh::lean_ctor_get(v___x_6032_, 0);
                            v_isSharedCheck_6042_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6032_)) as u8;
                            if v_isSharedCheck_6042_ == 0 {
                                v___x_6035_ = v___x_6032_;
                                v_isShared_6036_ = v_isSharedCheck_6042_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6033_);
                                crate::leanh::lean_dec(v___x_6032_);
                                v___x_6035_ = crate::leanh::lean_box(0);
                                v_isShared_6036_ = v_isSharedCheck_6042_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_struct_6020_);
                            v_a_6043_ = crate::leanh::lean_ctor_get(v___x_6032_, 0);
                            v_isSharedCheck_6050_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6032_)) as u8;
                            if v_isSharedCheck_6050_ == 0 {
                                v___x_6045_ = v___x_6032_;
                                v_isShared_6046_ = v_isSharedCheck_6050_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6043_);
                                crate::leanh::lean_dec(v___x_6032_);
                                v___x_6045_ = crate::leanh::lean_box(0);
                                v_isShared_6046_ = v_isSharedCheck_6050_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_struct_6020_);
                        crate::leanh::lean_dec_ref(v_params_6003_);
                        v_a_6051_ = crate::leanh::lean_ctor_get(v___x_6024_, 0);
                        v_isSharedCheck_6058_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6024_)) as u8;
                        if v_isSharedCheck_6058_ == 0 {
                            v___x_6053_ = v___x_6024_;
                            v_isShared_6054_ = v_isSharedCheck_6058_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6051_);
                            crate::leanh::lean_dec(v___x_6024_);
                            v___x_6053_ = crate::leanh::lean_box(0);
                            v_isShared_6054_ = v_isSharedCheck_6058_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_struct_6020_);
                    crate::leanh::lean_dec_ref(v_params_6003_);
                    v_a_6059_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                    v_isSharedCheck_6066_ = (!crate::leanh::lean_is_exclusive(v___x_6022_)) as u8;
                    if v_isSharedCheck_6066_ == 0 {
                        v___x_6061_ = v___x_6022_;
                        v_isShared_6062_ = v_isSharedCheck_6066_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6059_);
                        crate::leanh::lean_dec(v___x_6022_);
                        v___x_6061_ = crate::leanh::lean_box(0);
                        v_isShared_6062_ = v_isSharedCheck_6066_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6037_ = (crate::leanh::lean_unbox(v_a_6033_) as u8);
                crate::leanh::lean_dec(v_a_6033_);
                if v___x_6037_ == 0 {
                    crate::leanh::lean_del_object(v___x_6035_);
                    crate::leanh::lean_dec_ref(v_struct_6020_);
                    state = 1;
                    continue;
                } else {
                    v___x_6038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6038_, 0, v_struct_6020_);
                    if v_isShared_6036_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6035_, 0, v___x_6038_);
                        v___x_6040_ = v___x_6035_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6041_, 0, v___x_6038_);
                        v___x_6040_ = v_reuseFailAlloc_6041_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_6040_;
            }
            6 => {
                if v_isShared_6046_ == 0 {
                    v___x_6048_ = v___x_6045_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6049_, 0, v_a_6043_);
                    v___x_6048_ = v_reuseFailAlloc_6049_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6048_;
            }
            8 => {
                if v_isShared_6054_ == 0 {
                    v___x_6056_ = v___x_6053_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
                    v___x_6056_ = v_reuseFailAlloc_6057_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6056_;
            }
            10 => {
                if v_isShared_6062_ == 0 {
                    v___x_6064_ = v___x_6061_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
                    v___x_6064_ = v_reuseFailAlloc_6065_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6064_;
            }
            12 => {
                if v___y_6068_ == 0 {
                    crate::leanh::lean_dec_ref(v_struct_6020_);
                    crate::leanh::lean_dec_ref_known(v_e_6005_, 3);
                    crate::leanh::lean_dec_ref(v_params_6003_);
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_x3f_6006_) == 0 {
                        state = 3;
                        continue;
                    } else {
                        v_val_6069_ = crate::leanh::lean_ctor_get(v_x_x3f_6006_, 0);
                        v___x_6070_ = lean_expr_eqv(v_val_6069_, v_struct_6020_);
                        if v___x_6070_ == 0 {
                            crate::leanh::lean_dec_ref(v_struct_6020_);
                            crate::leanh::lean_dec_ref_known(v_e_6005_, 3);
                            crate::leanh::lean_dec_ref(v_params_6003_);
                            state = 1;
                            continue;
                        } else {
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_a_6076_) == 1 {
                    v_val_6110_ = crate::leanh::lean_ctor_get(v_a_6076_, 0);
                    crate::leanh::lean_inc(v_val_6110_);
                    crate::leanh::lean_dec_ref_known(v_a_6076_, 1);
                    v_ctorName_6111_ = crate::leanh::lean_ctor_get(v_val_6110_, 0);
                    crate::leanh::lean_inc(v_ctorName_6111_);
                    v_numParams_6112_ = crate::leanh::lean_ctor_get(v_val_6110_, 1);
                    crate::leanh::lean_inc(v_numParams_6112_);
                    v_i_6113_ = crate::leanh::lean_ctor_get(v_val_6110_, 2);
                    crate::leanh::lean_inc(v_i_6113_);
                    crate::leanh::lean_dec(v_val_6110_);
                    v___x_6123_ = lean_name_eq(v_ctorName_6111_, v_ctor_6001_);
                    crate::leanh::lean_dec(v_ctorName_6111_);
                    if v___x_6123_ == 0 {
                        crate::leanh::lean_dec(v_i_6113_);
                        v___y_6115_ = v___x_6123_;
                        state = 20;
                        continue;
                    } else {
                        v___x_6124_ = lean_nat_dec_eq(v_i_6113_, v_idx_6004_);
                        crate::leanh::lean_dec(v_i_6113_);
                        v___y_6115_ = v___x_6124_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6078_);
                    crate::leanh::lean_dec(v_a_6076_);
                    crate::leanh::lean_dec_ref(v_e_6005_);
                    crate::leanh::lean_dec_ref(v_params_6003_);
                    state = 2;
                    continue;
                }
            }
            14 => {
                v___x_6083_ = l_Lean_Expr_appFn_x21(v_e_6005_);
                crate::leanh::lean_dec_ref(v_e_6005_);
                v_dummy_6084_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once), _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
                v_nargs_6085_ = l_Lean_Expr_getAppNumArgs(v___x_6083_);
                crate::leanh::lean_inc(v_nargs_6085_);
                v___x_6086_ = lean_mk_array(v_nargs_6085_, v_dummy_6084_);
                v___x_6087_ = lean_nat_sub(v_nargs_6085_, v___y_6081_);
                crate::leanh::lean_dec(v_nargs_6085_);
                v___x_6088_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v___x_6083_,
                    v___x_6086_,
                    v___x_6087_,
                );
                v___x_6089_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_sameParams(
                    v_params_6003_,
                    v___x_6088_,
                    v_a_6007_,
                    v_a_6008_,
                    v_a_6009_,
                    v_a_6010_,
                );
                if crate::leanh::lean_obj_tag(v___x_6089_) == 0 {
                    v_a_6090_ = crate::leanh::lean_ctor_get(v___x_6089_, 0);
                    v_isSharedCheck_6101_ = (!crate::leanh::lean_is_exclusive(v___x_6089_)) as u8;
                    if v_isSharedCheck_6101_ == 0 {
                        v___x_6092_ = v___x_6089_;
                        v_isShared_6093_ = v_isSharedCheck_6101_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6090_);
                        crate::leanh::lean_dec(v___x_6089_);
                        v___x_6092_ = crate::leanh::lean_box(0);
                        v_isShared_6093_ = v_isSharedCheck_6101_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6082_);
                    crate::leanh::lean_del_object(v___x_6078_);
                    v_a_6102_ = crate::leanh::lean_ctor_get(v___x_6089_, 0);
                    v_isSharedCheck_6109_ = (!crate::leanh::lean_is_exclusive(v___x_6089_)) as u8;
                    if v_isSharedCheck_6109_ == 0 {
                        v___x_6104_ = v___x_6089_;
                        v_isShared_6105_ = v_isSharedCheck_6109_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6102_);
                        crate::leanh::lean_dec(v___x_6089_);
                        v___x_6104_ = crate::leanh::lean_box(0);
                        v_isShared_6105_ = v_isSharedCheck_6109_;
                        state = 18;
                        continue;
                    }
                }
            }
            15 => {
                v___x_6094_ = (crate::leanh::lean_unbox(v_a_6090_) as u8);
                crate::leanh::lean_dec(v_a_6090_);
                if v___x_6094_ == 0 {
                    crate::leanh::lean_del_object(v___x_6092_);
                    crate::leanh::lean_dec_ref(v___y_6082_);
                    crate::leanh::lean_del_object(v___x_6078_);
                    state = 2;
                    continue;
                } else {
                    if v_isShared_6079_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6078_, 1);
                        crate::leanh::lean_ctor_set(v___x_6078_, 0, v___y_6082_);
                        v___x_6096_ = v___x_6078_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___y_6082_);
                        v___x_6096_ = v_reuseFailAlloc_6100_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_6093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6092_, 0, v___x_6096_);
                    v___x_6098_ = v___x_6092_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6099_, 0, v___x_6096_);
                    v___x_6098_ = v_reuseFailAlloc_6099_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6098_;
            }
            18 => {
                if v_isShared_6105_ == 0 {
                    v___x_6107_ = v___x_6104_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6108_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_a_6102_);
                    v___x_6107_ = v_reuseFailAlloc_6108_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6107_;
            }
            20 => {
                if v___y_6115_ == 0 {
                    crate::leanh::lean_dec(v_numParams_6112_);
                    crate::leanh::lean_del_object(v___x_6078_);
                    crate::leanh::lean_dec_ref(v_e_6005_);
                    crate::leanh::lean_dec_ref(v_params_6003_);
                    state = 2;
                    continue;
                } else {
                    v___x_6116_ = l_Lean_Expr_getAppNumArgs(v_e_6005_);
                    v___x_6117_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6118_ = lean_nat_add(v_numParams_6112_, v___x_6117_);
                    crate::leanh::lean_dec(v_numParams_6112_);
                    v___x_6119_ = lean_nat_dec_eq(v___x_6116_, v___x_6118_);
                    crate::leanh::lean_dec(v___x_6118_);
                    crate::leanh::lean_dec(v___x_6116_);
                    if v___x_6119_ == 0 {
                        crate::leanh::lean_del_object(v___x_6078_);
                        crate::leanh::lean_dec_ref(v_e_6005_);
                        crate::leanh::lean_dec_ref(v_params_6003_);
                        state = 2;
                        continue;
                    } else {
                        v___x_6120_ = l_Lean_Expr_appArg_x21(v_e_6005_);
                        if crate::leanh::lean_obj_tag(v_x_x3f_6006_) == 0 {
                            v___y_6081_ = v___x_6117_;
                            v___y_6082_ = v___x_6120_;
                            state = 14;
                            continue;
                        } else {
                            v_val_6121_ = crate::leanh::lean_ctor_get(v_x_x3f_6006_, 0);
                            v___x_6122_ = lean_expr_eqv(v_val_6121_, v___x_6120_);
                            if v___x_6122_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_6120_);
                                crate::leanh::lean_del_object(v___x_6078_);
                                crate::leanh::lean_dec_ref(v_e_6005_);
                                crate::leanh::lean_dec_ref(v_params_6003_);
                                state = 2;
                                continue;
                            } else {
                                v___y_6081_ = v___x_6117_;
                                v___y_6082_ = v___x_6120_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___boxed(
    mut v_ctor_6126_: *mut crate::leanh::LeanObject,
    mut v_induct_6127_: *mut crate::leanh::LeanObject,
    mut v_params_6128_: *mut crate::leanh::LeanObject,
    mut v_idx_6129_: *mut crate::leanh::LeanObject,
    mut v_e_6130_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_6131_: *mut crate::leanh::LeanObject,
    mut v_a_6132_: *mut crate::leanh::LeanObject,
    mut v_a_6133_: *mut crate::leanh::LeanObject,
    mut v_a_6134_: *mut crate::leanh::LeanObject,
    mut v_a_6135_: *mut crate::leanh::LeanObject,
    mut v_a_6136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6137_ = l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(
        v_ctor_6126_,
        v_induct_6127_,
        v_params_6128_,
        v_idx_6129_,
        v_e_6130_,
        v_x_x3f_6131_,
        v_a_6132_,
        v_a_6133_,
        v_a_6134_,
        v_a_6135_,
    );
    crate::leanh::lean_dec(v_a_6135_);
    crate::leanh::lean_dec_ref(v_a_6134_);
    crate::leanh::lean_dec(v_a_6133_);
    crate::leanh::lean_dec_ref(v_a_6132_);
    crate::leanh::lean_dec(v_x_x3f_6131_);
    crate::leanh::lean_dec(v_idx_6129_);
    crate::leanh::lean_dec(v_induct_6127_);
    crate::leanh::lean_dec(v_ctor_6126_);
    return v_res_6137_;
}
pub unsafe fn l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(
    mut v_constName_6138_: *mut crate::leanh::LeanObject,
    mut v___y_6139_: *mut crate::leanh::LeanObject,
    mut v___y_6140_: *mut crate::leanh::LeanObject,
    mut v___y_6141_: *mut crate::leanh::LeanObject,
    mut v___y_6142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: u8 = 0;
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6154_: u8 = 0;
    let mut v_kind_6155_: u8 = 0;
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6160_: u8 = 0;
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6144_ = lean_st_ref_get(v___y_6142_);
                v_env_6148_ = crate::leanh::lean_ctor_get(v___x_6144_, 0);
                crate::leanh::lean_inc_ref(v_env_6148_);
                crate::leanh::lean_dec(v___x_6144_);
                v___x_6149_ = 0;
                v___x_6150_ =
                    l_Lean_Environment_findAsync_x3f(v_env_6148_, v_constName_6138_, v___x_6149_);
                if crate::leanh::lean_obj_tag(v___x_6150_) == 1 {
                    v_val_6151_ = crate::leanh::lean_ctor_get(v___x_6150_, 0);
                    v_isSharedCheck_6170_ = (!crate::leanh::lean_is_exclusive(v___x_6150_)) as u8;
                    if v_isSharedCheck_6170_ == 0 {
                        v___x_6153_ = v___x_6150_;
                        v_isShared_6154_ = v_isSharedCheck_6170_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6151_);
                        crate::leanh::lean_dec(v___x_6150_);
                        v___x_6153_ = crate::leanh::lean_box(0);
                        v_isShared_6154_ = v_isSharedCheck_6170_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6150_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6146_ = crate::leanh::lean_box(0);
                v___x_6147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6147_, 0, v___x_6146_);
                return v___x_6147_;
            }
            2 => {
                v_kind_6155_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_6151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_6155_ == 6 {
                    v___x_6156_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_6151_);
                    if crate::leanh::lean_obj_tag(v___x_6156_) == 6 {
                        v_val_6157_ = crate::leanh::lean_ctor_get(v___x_6156_, 0);
                        v_isSharedCheck_6167_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6156_)) as u8;
                        if v_isSharedCheck_6167_ == 0 {
                            v___x_6159_ = v___x_6156_;
                            v_isShared_6160_ = v_isSharedCheck_6167_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6157_);
                            crate::leanh::lean_dec(v___x_6156_);
                            v___x_6159_ = crate::leanh::lean_box(0);
                            v_isShared_6160_ = v_isSharedCheck_6167_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6156_);
                        crate::leanh::lean_del_object(v___x_6153_);
                        v___x_6168_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1___closed__5);
                        v___x_6169_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkProjections_spec__1_spec__1(v___x_6168_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_);
                        return v___x_6169_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6153_);
                    crate::leanh::lean_dec(v_val_6151_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_6154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6153_, 0, v_val_6157_);
                    v___x_6162_ = v___x_6153_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_val_6157_);
                    v___x_6162_ = v_reuseFailAlloc_6166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6160_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6159_, 0);
                    crate::leanh::lean_ctor_set(v___x_6159_, 0, v___x_6162_);
                    v___x_6164_ = v___x_6159_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6165_, 0, v___x_6162_);
                    v___x_6164_ = v_reuseFailAlloc_6165_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0___boxed(
    mut v_constName_6171_: *mut crate::leanh::LeanObject,
    mut v___y_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6177_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(
        v_constName_6171_,
        v___y_6172_,
        v___y_6173_,
        v___y_6174_,
        v___y_6175_,
    );
    crate::leanh::lean_dec(v___y_6175_);
    crate::leanh::lean_dec_ref(v___y_6174_);
    crate::leanh::lean_dec(v___y_6173_);
    crate::leanh::lean_dec_ref(v___y_6172_);
    return v_res_6177_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(
    mut v_upperBound_6186_: *mut crate::leanh::LeanObject,
    mut v___x_6187_: *mut crate::leanh::LeanObject,
    mut v___x_6188_: *mut crate::leanh::LeanObject,
    mut v_declName_6189_: *mut crate::leanh::LeanObject,
    mut v___x_6190_: *mut crate::leanh::LeanObject,
    mut v___x_6191_: *mut crate::leanh::LeanObject,
    mut v_a_6192_: *mut crate::leanh::LeanObject,
    mut v_val_6193_: *mut crate::leanh::LeanObject,
    mut v_a_6194_: *mut crate::leanh::LeanObject,
    mut v_b_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6201_: u8 = 0;
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6210_: u8 = 0;
    let mut v_val_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6225_: u8 = 0;
    let mut v_a_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6229_: u8 = 0;
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6201_ = lean_nat_dec_lt(v_a_6194_, v_upperBound_6186_);
                if v___x_6201_ == 0 {
                    crate::leanh::lean_dec(v_a_6194_);
                    crate::leanh::lean_dec_ref(v___x_6191_);
                    v___x_6202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6202_, 0, v_b_6195_);
                    return v___x_6202_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_6195_);
                    v___x_6203_ = l_Lean_instInhabitedExpr;
                    v___x_6204_ = lean_nat_add(v___x_6187_, v_a_6194_);
                    v___x_6205_ = lean_array_get_borrowed(v___x_6203_, v___x_6188_, v___x_6204_);
                    crate::leanh::lean_dec(v___x_6204_);
                    crate::leanh::lean_inc(v___x_6205_);
                    crate::leanh::lean_inc_ref(v___x_6191_);
                    v___x_6206_ =
                        l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(
                            v_declName_6189_,
                            v___x_6190_,
                            v___x_6191_,
                            v_a_6194_,
                            v___x_6205_,
                            v_a_6192_,
                            v___y_6196_,
                            v___y_6197_,
                            v___y_6198_,
                            v___y_6199_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6206_) == 0 {
                        v_a_6207_ = crate::leanh::lean_ctor_get(v___x_6206_, 0);
                        v_isSharedCheck_6225_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6206_)) as u8;
                        if v_isSharedCheck_6225_ == 0 {
                            v___x_6209_ = v___x_6206_;
                            v_isShared_6210_ = v_isSharedCheck_6225_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6207_);
                            crate::leanh::lean_dec(v___x_6206_);
                            v___x_6209_ = crate::leanh::lean_box(0);
                            v_isShared_6210_ = v_isSharedCheck_6225_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6194_);
                        crate::leanh::lean_dec_ref(v___x_6191_);
                        v_a_6226_ = crate::leanh::lean_ctor_get(v___x_6206_, 0);
                        v_isSharedCheck_6233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6206_)) as u8;
                        if v_isSharedCheck_6233_ == 0 {
                            v___x_6228_ = v___x_6206_;
                            v_isShared_6229_ = v_isSharedCheck_6233_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6226_);
                            crate::leanh::lean_dec(v___x_6206_);
                            v___x_6228_ = crate::leanh::lean_box(0);
                            v_isShared_6229_ = v_isSharedCheck_6233_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6207_) == 1 {
                    v_val_6211_ = crate::leanh::lean_ctor_get(v_a_6207_, 0);
                    crate::leanh::lean_inc(v_val_6211_);
                    crate::leanh::lean_dec_ref_known(v_a_6207_, 1);
                    v___x_6212_ = lean_expr_eqv(v_val_6211_, v_val_6193_);
                    crate::leanh::lean_dec(v_val_6211_);
                    if v___x_6212_ == 0 {
                        crate::leanh::lean_dec(v_a_6194_);
                        crate::leanh::lean_dec_ref(v___x_6191_);
                        v___x_6213_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1;
                        if v_isShared_6210_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6209_, 0, v___x_6213_);
                            v___x_6215_ = v___x_6209_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6216_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v___x_6213_);
                            v___x_6215_ = v_reuseFailAlloc_6216_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6209_);
                        v___x_6217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2;
                        v___x_6218_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6219_ = lean_nat_add(v_a_6194_, v___x_6218_);
                        crate::leanh::lean_dec(v_a_6194_);
                        v_a_6194_ = v___x_6219_;
                        v_b_6195_ = v___x_6217_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6207_);
                    crate::leanh::lean_dec(v_a_6194_);
                    crate::leanh::lean_dec_ref(v___x_6191_);
                    v___x_6221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__1;
                    if v_isShared_6210_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6209_, 0, v___x_6221_);
                        v___x_6223_ = v___x_6209_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6224_, 0, v___x_6221_);
                        v___x_6223_ = v_reuseFailAlloc_6224_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6215_;
            }
            3 => {
                return v___x_6223_;
            }
            4 => {
                if v_isShared_6229_ == 0 {
                    v___x_6231_ = v___x_6228_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_a_6226_);
                    v___x_6231_ = v_reuseFailAlloc_6232_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___boxed(
    mut v_upperBound_6234_: *mut crate::leanh::LeanObject,
    mut v___x_6235_: *mut crate::leanh::LeanObject,
    mut v___x_6236_: *mut crate::leanh::LeanObject,
    mut v_declName_6237_: *mut crate::leanh::LeanObject,
    mut v___x_6238_: *mut crate::leanh::LeanObject,
    mut v___x_6239_: *mut crate::leanh::LeanObject,
    mut v_a_6240_: *mut crate::leanh::LeanObject,
    mut v_val_6241_: *mut crate::leanh::LeanObject,
    mut v_a_6242_: *mut crate::leanh::LeanObject,
    mut v_b_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
    mut v___y_6248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(
        v_upperBound_6234_,
        v___x_6235_,
        v___x_6236_,
        v_declName_6237_,
        v___x_6238_,
        v___x_6239_,
        v_a_6240_,
        v_val_6241_,
        v_a_6242_,
        v_b_6243_,
        v___y_6244_,
        v___y_6245_,
        v___y_6246_,
        v___y_6247_,
    );
    crate::leanh::lean_dec(v___y_6247_);
    crate::leanh::lean_dec_ref(v___y_6246_);
    crate::leanh::lean_dec(v___y_6245_);
    crate::leanh::lean_dec_ref(v___y_6244_);
    crate::leanh::lean_dec_ref(v_val_6241_);
    crate::leanh::lean_dec(v_a_6240_);
    crate::leanh::lean_dec(v___x_6238_);
    crate::leanh::lean_dec(v_declName_6237_);
    crate::leanh::lean_dec_ref(v___x_6236_);
    crate::leanh::lean_dec(v___x_6235_);
    crate::leanh::lean_dec(v_upperBound_6234_);
    return v_res_6249_;
}
pub unsafe fn l_Lean_Meta_etaStruct_x3f(
    mut v_e_6250_: *mut crate::leanh::LeanObject,
    mut v_p_6251_: *mut crate::leanh::LeanObject,
    mut v_a_6252_: *mut crate::leanh::LeanObject,
    mut v_a_6253_: *mut crate::leanh::LeanObject,
    mut v_a_6254_: *mut crate::leanh::LeanObject,
    mut v_a_6255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6263_: u8 = 0;
    let mut v_val_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_induct_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: u8 = 0;
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: u8 = 0;
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v_val_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6302_: u8 = 0;
    let mut v_fst_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6323_: u8 = 0;
    let mut v___x_6324_: u8 = 0;
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: u8 = 0;
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6332_: u8 = 0;
    let mut v_a_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6257_ = l_Lean_Expr_getAppFn(v_e_6250_);
                if crate::leanh::lean_obj_tag(v___x_6257_) == 4 {
                    v_declName_6258_ = crate::leanh::lean_ctor_get(v___x_6257_, 0);
                    crate::leanh::lean_inc_n(v_declName_6258_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6257_, 2);
                    v___x_6259_ = l_Lean_isCtor_x3f___at___00Lean_Meta_etaStruct_x3f_spec__0(
                        v_declName_6258_,
                        v_a_6252_,
                        v_a_6253_,
                        v_a_6254_,
                        v_a_6255_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6259_) == 0 {
                        v_a_6260_ = crate::leanh::lean_ctor_get(v___x_6259_, 0);
                        v_isSharedCheck_6332_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6259_)) as u8;
                        if v_isSharedCheck_6332_ == 0 {
                            v___x_6262_ = v___x_6259_;
                            v_isShared_6263_ = v_isSharedCheck_6332_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6260_);
                            crate::leanh::lean_dec(v___x_6259_);
                            v___x_6262_ = crate::leanh::lean_box(0);
                            v_isShared_6263_ = v_isSharedCheck_6332_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_6258_);
                        crate::leanh::lean_dec_ref(v_p_6251_);
                        crate::leanh::lean_dec_ref(v_e_6250_);
                        v_a_6333_ = crate::leanh::lean_ctor_get(v___x_6259_, 0);
                        v_isSharedCheck_6340_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6259_)) as u8;
                        if v_isSharedCheck_6340_ == 0 {
                            v___x_6335_ = v___x_6259_;
                            v_isShared_6336_ = v_isSharedCheck_6340_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6333_);
                            crate::leanh::lean_dec(v___x_6259_);
                            v___x_6335_ = crate::leanh::lean_box(0);
                            v_isShared_6336_ = v_isSharedCheck_6340_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_6257_);
                    crate::leanh::lean_dec_ref(v_p_6251_);
                    crate::leanh::lean_dec_ref(v_e_6250_);
                    v___x_6341_ = crate::leanh::lean_box(0);
                    v___x_6342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6342_, 0, v___x_6341_);
                    return v___x_6342_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6260_) == 1 {
                    v_val_6264_ = crate::leanh::lean_ctor_get(v_a_6260_, 0);
                    crate::leanh::lean_inc(v_val_6264_);
                    crate::leanh::lean_dec_ref_known(v_a_6260_, 1);
                    v_induct_6265_ = crate::leanh::lean_ctor_get(v_val_6264_, 1);
                    crate::leanh::lean_inc_n(v_induct_6265_, 2);
                    v_numParams_6266_ = crate::leanh::lean_ctor_get(v_val_6264_, 3);
                    crate::leanh::lean_inc(v_numParams_6266_);
                    v_numFields_6267_ = crate::leanh::lean_ctor_get(v_val_6264_, 4);
                    crate::leanh::lean_inc(v_numFields_6267_);
                    crate::leanh::lean_dec(v_val_6264_);
                    v___x_6268_ = crate::leanh::lean_apply_1(v_p_6251_, v_induct_6265_);
                    v___x_6269_ = (crate::leanh::lean_unbox(v___x_6268_) as u8);
                    if v___x_6269_ == 0 {
                        crate::leanh::lean_dec(v_numFields_6267_);
                        crate::leanh::lean_dec(v_numParams_6266_);
                        crate::leanh::lean_dec(v_induct_6265_);
                        crate::leanh::lean_dec(v_declName_6258_);
                        crate::leanh::lean_dec_ref(v_e_6250_);
                        v___x_6270_ = crate::leanh::lean_box(0);
                        if v_isShared_6263_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6262_, 0, v___x_6270_);
                            v___x_6272_ = v___x_6262_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6273_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6273_, 0, v___x_6270_);
                            v___x_6272_ = v_reuseFailAlloc_6273_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_6274_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6324_ = lean_nat_dec_lt(v___x_6274_, v_numFields_6267_);
                        if v___x_6324_ == 0 {
                            v___y_6276_ = v___x_6324_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6325_ = l_Lean_Expr_getAppNumArgs(v_e_6250_);
                            v___x_6326_ = lean_nat_add(v_numParams_6266_, v_numFields_6267_);
                            v___x_6327_ = lean_nat_dec_eq(v___x_6325_, v___x_6326_);
                            crate::leanh::lean_dec(v___x_6326_);
                            crate::leanh::lean_dec(v___x_6325_);
                            v___y_6276_ = v___x_6327_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6260_);
                    crate::leanh::lean_dec(v_declName_6258_);
                    crate::leanh::lean_dec_ref(v_p_6251_);
                    crate::leanh::lean_dec_ref(v_e_6250_);
                    v___x_6328_ = crate::leanh::lean_box(0);
                    if v_isShared_6263_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6262_, 0, v___x_6328_);
                        v___x_6330_ = v___x_6262_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6331_, 0, v___x_6328_);
                        v___x_6330_ = v_reuseFailAlloc_6331_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6272_;
            }
            3 => {
                if v___y_6276_ == 0 {
                    crate::leanh::lean_dec(v_numFields_6267_);
                    crate::leanh::lean_dec(v_numParams_6266_);
                    crate::leanh::lean_dec(v_induct_6265_);
                    crate::leanh::lean_dec(v_declName_6258_);
                    crate::leanh::lean_dec_ref(v_e_6250_);
                    v___x_6277_ = crate::leanh::lean_box(0);
                    if v_isShared_6263_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6262_, 0, v___x_6277_);
                        v___x_6279_ = v___x_6262_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6280_, 0, v___x_6277_);
                        v___x_6279_ = v_reuseFailAlloc_6280_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6262_);
                    v_dummy_6281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once), _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
                    v_nargs_6282_ = l_Lean_Expr_getAppNumArgs(v_e_6250_);
                    crate::leanh::lean_inc(v_nargs_6282_);
                    v___x_6283_ = lean_mk_array(v_nargs_6282_, v_dummy_6281_);
                    v___x_6284_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6285_ = lean_nat_sub(v_nargs_6282_, v___x_6284_);
                    crate::leanh::lean_dec(v_nargs_6282_);
                    v___x_6286_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_6250_,
                        v___x_6283_,
                        v___x_6285_,
                    );
                    crate::leanh::lean_inc(v_numParams_6266_);
                    v___x_6287_ =
                        l_Array_extract___redArg(v___x_6286_, v___x_6274_, v_numParams_6266_);
                    v___x_6288_ = l_Lean_instInhabitedExpr;
                    v___x_6289_ = lean_array_get(v___x_6288_, v___x_6286_, v_numParams_6266_);
                    v___x_6290_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v___x_6287_);
                    v___x_6291_ =
                        l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr(
                            v_declName_6258_,
                            v_induct_6265_,
                            v___x_6287_,
                            v___x_6274_,
                            v___x_6289_,
                            v___x_6290_,
                            v_a_6252_,
                            v_a_6253_,
                            v_a_6254_,
                            v_a_6255_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6291_) == 0 {
                        v_a_6292_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                        v_isSharedCheck_6323_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                        if v_isSharedCheck_6323_ == 0 {
                            v___x_6294_ = v___x_6291_;
                            v_isShared_6295_ = v_isSharedCheck_6323_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6292_);
                            crate::leanh::lean_dec(v___x_6291_);
                            v___x_6294_ = crate::leanh::lean_box(0);
                            v_isShared_6295_ = v_isSharedCheck_6323_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6287_);
                        crate::leanh::lean_dec_ref(v___x_6286_);
                        crate::leanh::lean_dec(v_numFields_6267_);
                        crate::leanh::lean_dec(v_numParams_6266_);
                        crate::leanh::lean_dec(v_induct_6265_);
                        crate::leanh::lean_dec(v_declName_6258_);
                        return v___x_6291_;
                    }
                }
            }
            4 => {
                return v___x_6279_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_6292_) == 1 {
                    crate::leanh::lean_del_object(v___x_6294_);
                    v_val_6296_ = crate::leanh::lean_ctor_get(v_a_6292_, 0);
                    v___x_6297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg___closed__2;
                    v___x_6298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(v_numFields_6267_, v_numParams_6266_, v___x_6286_, v_declName_6258_, v_induct_6265_, v___x_6287_, v_a_6292_, v_val_6296_, v___x_6284_, v___x_6297_, v_a_6252_, v_a_6253_, v_a_6254_, v_a_6255_);
                    crate::leanh::lean_dec(v_induct_6265_);
                    crate::leanh::lean_dec(v_declName_6258_);
                    crate::leanh::lean_dec_ref(v___x_6286_);
                    crate::leanh::lean_dec(v_numParams_6266_);
                    crate::leanh::lean_dec(v_numFields_6267_);
                    if crate::leanh::lean_obj_tag(v___x_6298_) == 0 {
                        v_a_6299_ = crate::leanh::lean_ctor_get(v___x_6298_, 0);
                        v_isSharedCheck_6311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6298_)) as u8;
                        if v_isSharedCheck_6311_ == 0 {
                            v___x_6301_ = v___x_6298_;
                            v_isShared_6302_ = v_isSharedCheck_6311_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6299_);
                            crate::leanh::lean_dec(v___x_6298_);
                            v___x_6301_ = crate::leanh::lean_box(0);
                            v_isShared_6302_ = v_isSharedCheck_6311_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_6292_, 1);
                        v_a_6312_ = crate::leanh::lean_ctor_get(v___x_6298_, 0);
                        v_isSharedCheck_6319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6298_)) as u8;
                        if v_isSharedCheck_6319_ == 0 {
                            v___x_6314_ = v___x_6298_;
                            v_isShared_6315_ = v_isSharedCheck_6319_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6312_);
                            crate::leanh::lean_dec(v___x_6298_);
                            v___x_6314_ = crate::leanh::lean_box(0);
                            v_isShared_6315_ = v_isSharedCheck_6319_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6292_);
                    crate::leanh::lean_dec_ref(v___x_6287_);
                    crate::leanh::lean_dec_ref(v___x_6286_);
                    crate::leanh::lean_dec(v_numFields_6267_);
                    crate::leanh::lean_dec(v_numParams_6266_);
                    crate::leanh::lean_dec(v_induct_6265_);
                    crate::leanh::lean_dec(v_declName_6258_);
                    if v_isShared_6295_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6294_, 0, v___x_6290_);
                        v___x_6321_ = v___x_6294_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6322_, 0, v___x_6290_);
                        v___x_6321_ = v_reuseFailAlloc_6322_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_6303_ = crate::leanh::lean_ctor_get(v_a_6299_, 0);
                crate::leanh::lean_inc(v_fst_6303_);
                crate::leanh::lean_dec(v_a_6299_);
                if crate::leanh::lean_obj_tag(v_fst_6303_) == 0 {
                    if v_isShared_6302_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6301_, 0, v_a_6292_);
                        v___x_6305_ = v___x_6301_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6292_);
                        v___x_6305_ = v_reuseFailAlloc_6306_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6292_, 1);
                    v_val_6307_ = crate::leanh::lean_ctor_get(v_fst_6303_, 0);
                    crate::leanh::lean_inc(v_val_6307_);
                    crate::leanh::lean_dec_ref_known(v_fst_6303_, 1);
                    if v_isShared_6302_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6301_, 0, v_val_6307_);
                        v___x_6309_ = v___x_6301_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_val_6307_);
                        v___x_6309_ = v_reuseFailAlloc_6310_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6305_;
            }
            8 => {
                return v___x_6309_;
            }
            9 => {
                if v_isShared_6315_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
                    v___x_6317_ = v_reuseFailAlloc_6318_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6317_;
            }
            11 => {
                return v___x_6321_;
            }
            12 => {
                return v___x_6330_;
            }
            13 => {
                if v_isShared_6336_ == 0 {
                    v___x_6338_ = v___x_6335_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6333_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_etaStruct_x3f___boxed(
    mut v_e_6343_: *mut crate::leanh::LeanObject,
    mut v_p_6344_: *mut crate::leanh::LeanObject,
    mut v_a_6345_: *mut crate::leanh::LeanObject,
    mut v_a_6346_: *mut crate::leanh::LeanObject,
    mut v_a_6347_: *mut crate::leanh::LeanObject,
    mut v_a_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6350_ = l_Lean_Meta_etaStruct_x3f(
        v_e_6343_, v_p_6344_, v_a_6345_, v_a_6346_, v_a_6347_, v_a_6348_,
    );
    crate::leanh::lean_dec(v_a_6348_);
    crate::leanh::lean_dec_ref(v_a_6347_);
    crate::leanh::lean_dec(v_a_6346_);
    crate::leanh::lean_dec_ref(v_a_6345_);
    return v_res_6350_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(
    mut v_upperBound_6351_: *mut crate::leanh::LeanObject,
    mut v___x_6352_: *mut crate::leanh::LeanObject,
    mut v___x_6353_: *mut crate::leanh::LeanObject,
    mut v_declName_6354_: *mut crate::leanh::LeanObject,
    mut v___x_6355_: *mut crate::leanh::LeanObject,
    mut v___x_6356_: *mut crate::leanh::LeanObject,
    mut v_a_6357_: *mut crate::leanh::LeanObject,
    mut v_val_6358_: *mut crate::leanh::LeanObject,
    mut v_inst_6359_: *mut crate::leanh::LeanObject,
    mut v_R_6360_: *mut crate::leanh::LeanObject,
    mut v_a_6361_: *mut crate::leanh::LeanObject,
    mut v_b_6362_: *mut crate::leanh::LeanObject,
    mut v_c_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6369_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___redArg(
        v_upperBound_6351_,
        v___x_6352_,
        v___x_6353_,
        v_declName_6354_,
        v___x_6355_,
        v___x_6356_,
        v_a_6357_,
        v_val_6358_,
        v_a_6361_,
        v_b_6362_,
        v___y_6364_,
        v___y_6365_,
        v___y_6366_,
        v___y_6367_,
    );
    return v___x_6369_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_6370_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_6371_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_6372_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_6373_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_6374_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_6375_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_6376_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_val_6377_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_6378_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_R_6379_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_6380_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_b_6381_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_c_6382_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6383_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6384_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6385_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6386_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6387_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6388_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_etaStruct_x3f_spec__1(
        v_upperBound_6370_,
        v___x_6371_,
        v___x_6372_,
        v_declName_6373_,
        v___x_6374_,
        v___x_6375_,
        v_a_6376_,
        v_val_6377_,
        v_inst_6378_,
        v_R_6379_,
        v_a_6380_,
        v_b_6381_,
        v_c_6382_,
        v___y_6383_,
        v___y_6384_,
        v___y_6385_,
        v___y_6386_,
    );
    crate::leanh::lean_dec(v___y_6386_);
    crate::leanh::lean_dec_ref(v___y_6385_);
    crate::leanh::lean_dec(v___y_6384_);
    crate::leanh::lean_dec_ref(v___y_6383_);
    crate::leanh::lean_dec_ref(v_val_6377_);
    crate::leanh::lean_dec(v_a_6376_);
    crate::leanh::lean_dec(v___x_6374_);
    crate::leanh::lean_dec(v_declName_6373_);
    crate::leanh::lean_dec_ref(v___x_6372_);
    crate::leanh::lean_dec(v___x_6371_);
    crate::leanh::lean_dec(v_upperBound_6370_);
    return v_res_6388_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(
    mut v_e_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6392_: u8 = 0;
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6406_: u8 = 0;
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6412_: u8 = 0;
    let mut v_unused_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6392_ = l_Lean_Expr_hasMVar(v_e_6389_);
                if v___x_6392_ == 0 {
                    v___x_6393_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6393_, 0, v_e_6389_);
                    return v___x_6393_;
                } else {
                    v___x_6394_ = lean_st_ref_get(v___y_6390_);
                    v_mctx_6395_ = crate::leanh::lean_ctor_get(v___x_6394_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_6395_);
                    crate::leanh::lean_dec(v___x_6394_);
                    v___x_6396_ = l_Lean_instantiateMVarsCore(v_mctx_6395_, v_e_6389_);
                    v_fst_6397_ = crate::leanh::lean_ctor_get(v___x_6396_, 0);
                    crate::leanh::lean_inc(v_fst_6397_);
                    v_snd_6398_ = crate::leanh::lean_ctor_get(v___x_6396_, 1);
                    crate::leanh::lean_inc(v_snd_6398_);
                    crate::leanh::lean_dec_ref(v___x_6396_);
                    v___x_6399_ = lean_st_ref_take(v___y_6390_);
                    v_cache_6400_ = crate::leanh::lean_ctor_get(v___x_6399_, 1);
                    v_zetaDeltaFVarIds_6401_ = crate::leanh::lean_ctor_get(v___x_6399_, 2);
                    v_postponed_6402_ = crate::leanh::lean_ctor_get(v___x_6399_, 3);
                    v_diag_6403_ = crate::leanh::lean_ctor_get(v___x_6399_, 4);
                    v_isSharedCheck_6412_ = (!crate::leanh::lean_is_exclusive(v___x_6399_)) as u8;
                    if v_isSharedCheck_6412_ == 0 {
                        v_unused_6413_ = crate::leanh::lean_ctor_get(v___x_6399_, 0);
                        crate::leanh::lean_dec(v_unused_6413_);
                        v___x_6405_ = v___x_6399_;
                        v_isShared_6406_ = v_isSharedCheck_6412_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_6403_);
                        crate::leanh::lean_inc(v_postponed_6402_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_6401_);
                        crate::leanh::lean_inc(v_cache_6400_);
                        crate::leanh::lean_dec(v___x_6399_);
                        v___x_6405_ = crate::leanh::lean_box(0);
                        v_isShared_6406_ = v_isSharedCheck_6412_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6405_, 0, v_snd_6398_);
                    v___x_6408_ = v___x_6405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6411_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_snd_6398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 1, v_cache_6400_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6411_,
                        2,
                        v_zetaDeltaFVarIds_6401_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 3, v_postponed_6402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6411_, 4, v_diag_6403_);
                    v___x_6408_ = v_reuseFailAlloc_6411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6409_ = lean_st_ref_set(v___y_6390_, v___x_6408_);
                v___x_6410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6410_, 0, v_fst_6397_);
                return v___x_6410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg___boxed(
    mut v_e_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6417_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(
        v_e_6414_,
        v___y_6415_,
    );
    crate::leanh::lean_dec(v___y_6415_);
    return v_res_6417_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(
    mut v_e_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6424_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(
        v_e_6418_,
        v___y_6420_,
    );
    return v___x_6424_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___boxed(
    mut v_e_6425_: *mut crate::leanh::LeanObject,
    mut v___y_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6431_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0(
        v_e_6425_,
        v___y_6426_,
        v___y_6427_,
        v___y_6428_,
        v___y_6429_,
    );
    crate::leanh::lean_dec(v___y_6429_);
    crate::leanh::lean_dec_ref(v___y_6428_);
    crate::leanh::lean_dec(v___y_6427_);
    crate::leanh::lean_dec_ref(v___y_6426_);
    return v_res_6431_;
}
pub unsafe fn l_Lean_Meta_etaStructReduce___lam__0(
    mut v_x_6434_: *mut crate::leanh::LeanObject,
    mut v___y_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6440_ = l_Lean_Meta_etaStructReduce___lam__0___closed__0;
    v___x_6441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6441_, 0, v___x_6440_);
    return v___x_6441_;
}
pub unsafe fn l_Lean_Meta_etaStructReduce___lam__0___boxed(
    mut v_x_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6448_ = l_Lean_Meta_etaStructReduce___lam__0(
        v_x_6442_,
        v___y_6443_,
        v___y_6444_,
        v___y_6445_,
        v___y_6446_,
    );
    crate::leanh::lean_dec(v___y_6446_);
    crate::leanh::lean_dec_ref(v___y_6445_);
    crate::leanh::lean_dec(v___y_6444_);
    crate::leanh::lean_dec_ref(v___y_6443_);
    crate::leanh::lean_dec_ref(v_x_6442_);
    return v_res_6448_;
}
pub unsafe fn l_Lean_Meta_etaStructReduce___lam__1(
    mut v_p_6449_: *mut crate::leanh::LeanObject,
    mut v_e_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v_val_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6464_: u8 = 0;
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6471_: u8 = 0;
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6476_: u8 = 0;
    let mut v_a_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6480_: u8 = 0;
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6456_ = l_Lean_Meta_etaStruct_x3f(
                    v_e_6450_,
                    v_p_6449_,
                    v___y_6451_,
                    v___y_6452_,
                    v___y_6453_,
                    v___y_6454_,
                );
                if crate::leanh::lean_obj_tag(v___x_6456_) == 0 {
                    v_a_6457_ = crate::leanh::lean_ctor_get(v___x_6456_, 0);
                    v_isSharedCheck_6476_ = (!crate::leanh::lean_is_exclusive(v___x_6456_)) as u8;
                    if v_isSharedCheck_6476_ == 0 {
                        v___x_6459_ = v___x_6456_;
                        v_isShared_6460_ = v_isSharedCheck_6476_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6457_);
                        crate::leanh::lean_dec(v___x_6456_);
                        v___x_6459_ = crate::leanh::lean_box(0);
                        v_isShared_6460_ = v_isSharedCheck_6476_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6477_ = crate::leanh::lean_ctor_get(v___x_6456_, 0);
                    v_isSharedCheck_6484_ = (!crate::leanh::lean_is_exclusive(v___x_6456_)) as u8;
                    if v_isSharedCheck_6484_ == 0 {
                        v___x_6479_ = v___x_6456_;
                        v_isShared_6480_ = v_isSharedCheck_6484_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6477_);
                        crate::leanh::lean_dec(v___x_6456_);
                        v___x_6479_ = crate::leanh::lean_box(0);
                        v_isShared_6480_ = v_isSharedCheck_6484_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6457_) == 1 {
                    v_val_6461_ = crate::leanh::lean_ctor_get(v_a_6457_, 0);
                    v_isSharedCheck_6471_ = (!crate::leanh::lean_is_exclusive(v_a_6457_)) as u8;
                    if v_isSharedCheck_6471_ == 0 {
                        v___x_6463_ = v_a_6457_;
                        v_isShared_6464_ = v_isSharedCheck_6471_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6461_);
                        crate::leanh::lean_dec(v_a_6457_);
                        v___x_6463_ = crate::leanh::lean_box(0);
                        v_isShared_6464_ = v_isSharedCheck_6471_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6457_);
                    v___x_6472_ = l_Lean_Meta_etaStructReduce___lam__0___closed__0;
                    if v_isShared_6460_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6459_, 0, v___x_6472_);
                        v___x_6474_ = v___x_6459_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6475_, 0, v___x_6472_);
                        v___x_6474_ = v_reuseFailAlloc_6475_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6464_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6463_, 0);
                    v___x_6466_ = v___x_6463_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6470_, 0, v_val_6461_);
                    v___x_6466_ = v_reuseFailAlloc_6470_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6459_, 0, v___x_6466_);
                    v___x_6468_ = v___x_6459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6469_, 0, v___x_6466_);
                    v___x_6468_ = v_reuseFailAlloc_6469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6468_;
            }
            5 => {
                return v___x_6474_;
            }
            6 => {
                if v_isShared_6480_ == 0 {
                    v___x_6482_ = v___x_6479_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6483_, 0, v_a_6477_);
                    v___x_6482_ = v_reuseFailAlloc_6483_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_etaStructReduce___lam__1___boxed(
    mut v_p_6485_: *mut crate::leanh::LeanObject,
    mut v_e_6486_: *mut crate::leanh::LeanObject,
    mut v___y_6487_: *mut crate::leanh::LeanObject,
    mut v___y_6488_: *mut crate::leanh::LeanObject,
    mut v___y_6489_: *mut crate::leanh::LeanObject,
    mut v___y_6490_: *mut crate::leanh::LeanObject,
    mut v___y_6491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6492_ = l_Lean_Meta_etaStructReduce___lam__1(
        v_p_6485_,
        v_e_6486_,
        v___y_6487_,
        v___y_6488_,
        v___y_6489_,
        v___y_6490_,
    );
    crate::leanh::lean_dec(v___y_6490_);
    crate::leanh::lean_dec_ref(v___y_6489_);
    crate::leanh::lean_dec(v___y_6488_);
    crate::leanh::lean_dec_ref(v___y_6487_);
    return v_res_6492_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(
    mut v_00_u03b1_6493_: *mut crate::leanh::LeanObject,
    mut v_x_6494_: *mut crate::leanh::LeanObject,
    mut v___y_6495_: *mut crate::leanh::LeanObject,
    mut v___y_6496_: *mut crate::leanh::LeanObject,
    mut v___y_6497_: *mut crate::leanh::LeanObject,
    mut v___y_6498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6500_ = crate::leanh::lean_apply_1(v_x_6494_, crate::leanh::lean_box(0));
    v___x_6501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6501_, 0, v___x_6500_);
    return v___x_6501_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0___boxed(
    mut v_00_u03b1_6502_: *mut crate::leanh::LeanObject,
    mut v_x_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
    mut v___y_6507_: *mut crate::leanh::LeanObject,
    mut v___y_6508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6509_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(
        v_00_u03b1_6502_,
        v_x_6503_,
        v___y_6504_,
        v___y_6505_,
        v___y_6506_,
        v___y_6507_,
    );
    crate::leanh::lean_dec(v___y_6507_);
    crate::leanh::lean_dec_ref(v___y_6506_);
    crate::leanh::lean_dec(v___y_6505_);
    crate::leanh::lean_dec_ref(v___y_6504_);
    return v_res_6509_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(
    mut v_a_6510_: *mut crate::leanh::LeanObject,
    mut v_b_6511_: *mut crate::leanh::LeanObject,
    mut v_x_6512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6518_: u8 = 0;
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6512_) == 0 {
                    crate::leanh::lean_dec(v_b_6511_);
                    crate::leanh::lean_dec_ref(v_a_6510_);
                    return v_x_6512_;
                } else {
                    v_key_6513_ = crate::leanh::lean_ctor_get(v_x_6512_, 0);
                    v_value_6514_ = crate::leanh::lean_ctor_get(v_x_6512_, 1);
                    v_tail_6515_ = crate::leanh::lean_ctor_get(v_x_6512_, 2);
                    v_isSharedCheck_6527_ = (!crate::leanh::lean_is_exclusive(v_x_6512_)) as u8;
                    if v_isSharedCheck_6527_ == 0 {
                        v___x_6517_ = v_x_6512_;
                        v_isShared_6518_ = v_isSharedCheck_6527_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6515_);
                        crate::leanh::lean_inc(v_value_6514_);
                        crate::leanh::lean_inc(v_key_6513_);
                        crate::leanh::lean_dec(v_x_6512_);
                        v___x_6517_ = crate::leanh::lean_box(0);
                        v_isShared_6518_ = v_isSharedCheck_6527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6519_ = l_Lean_ExprStructEq_beq(v_key_6513_, v_a_6510_);
                if v___x_6519_ == 0 {
                    v___x_6520_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_6510_, v_b_6511_, v_tail_6515_);
                    if v_isShared_6518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6517_, 2, v___x_6520_);
                        v___x_6522_ = v___x_6517_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6523_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6523_, 0, v_key_6513_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6523_, 1, v_value_6514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6523_, 2, v___x_6520_);
                        v___x_6522_ = v_reuseFailAlloc_6523_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_6514_);
                    crate::leanh::lean_dec(v_key_6513_);
                    if v_isShared_6518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6517_, 1, v_b_6511_);
                        crate::leanh::lean_ctor_set(v___x_6517_, 0, v_a_6510_);
                        v___x_6525_ = v___x_6517_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6526_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_a_6510_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 1, v_b_6511_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 2, v_tail_6515_);
                        v___x_6525_ = v_reuseFailAlloc_6526_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6522_;
            }
            3 => {
                return v___x_6525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(
    mut v_x_6528_: *mut crate::leanh::LeanObject,
    mut v_x_6529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6535_: u8 = 0;
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: u64 = 0;
    let mut v___x_6538_: u64 = 0;
    let mut v___x_6539_: u64 = 0;
    let mut v_fold_6540_: u64 = 0;
    let mut v___x_6541_: u64 = 0;
    let mut v___x_6542_: u64 = 0;
    let mut v___x_6543_: u64 = 0;
    let mut v___x_6544_: usize = 0;
    let mut v___x_6545_: usize = 0;
    let mut v___x_6546_: usize = 0;
    let mut v___x_6547_: usize = 0;
    let mut v___x_6548_: usize = 0;
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6529_) == 0 {
                    return v_x_6528_;
                } else {
                    v_key_6530_ = crate::leanh::lean_ctor_get(v_x_6529_, 0);
                    v_value_6531_ = crate::leanh::lean_ctor_get(v_x_6529_, 1);
                    v_tail_6532_ = crate::leanh::lean_ctor_get(v_x_6529_, 2);
                    v_isSharedCheck_6555_ = (!crate::leanh::lean_is_exclusive(v_x_6529_)) as u8;
                    if v_isSharedCheck_6555_ == 0 {
                        v___x_6534_ = v_x_6529_;
                        v_isShared_6535_ = v_isSharedCheck_6555_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6532_);
                        crate::leanh::lean_inc(v_value_6531_);
                        crate::leanh::lean_inc(v_key_6530_);
                        crate::leanh::lean_dec(v_x_6529_);
                        v___x_6534_ = crate::leanh::lean_box(0);
                        v_isShared_6535_ = v_isSharedCheck_6555_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6536_ = lean_array_get_size(v_x_6528_);
                v___x_6537_ = l_Lean_ExprStructEq_hash(v_key_6530_);
                v___x_6538_ = 32u64;
                v___x_6539_ = lean_uint64_shift_right(v___x_6537_, v___x_6538_);
                v_fold_6540_ = lean_uint64_xor(v___x_6537_, v___x_6539_);
                v___x_6541_ = 16u64;
                v___x_6542_ = lean_uint64_shift_right(v_fold_6540_, v___x_6541_);
                v___x_6543_ = lean_uint64_xor(v_fold_6540_, v___x_6542_);
                v___x_6544_ = lean_uint64_to_usize(v___x_6543_);
                v___x_6545_ = lean_usize_of_nat(v___x_6536_);
                v___x_6546_ = 1usize;
                v___x_6547_ = lean_usize_sub(v___x_6545_, v___x_6546_);
                v___x_6548_ = lean_usize_land(v___x_6544_, v___x_6547_);
                v___x_6549_ = lean_array_uget_borrowed(v_x_6528_, v___x_6548_);
                crate::leanh::lean_inc(v___x_6549_);
                if v_isShared_6535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6534_, 2, v___x_6549_);
                    v___x_6551_ = v___x_6534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6554_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 0, v_key_6530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 1, v_value_6531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 2, v___x_6549_);
                    v___x_6551_ = v_reuseFailAlloc_6554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6552_ = lean_array_uset(v_x_6528_, v___x_6548_, v___x_6551_);
                v_x_6528_ = v___x_6552_;
                v_x_6529_ = v_tail_6532_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(
    mut v_i_6556_: *mut crate::leanh::LeanObject,
    mut v_source_6557_: *mut crate::leanh::LeanObject,
    mut v_target_6558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: u8 = 0;
    let mut v_es_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6559_ = lean_array_get_size(v_source_6557_);
                v___x_6560_ = lean_nat_dec_lt(v_i_6556_, v___x_6559_);
                if v___x_6560_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_6557_);
                    crate::leanh::lean_dec(v_i_6556_);
                    return v_target_6558_;
                } else {
                    v_es_6561_ = lean_array_fget(v_source_6557_, v_i_6556_);
                    v___x_6562_ = crate::leanh::lean_box(0);
                    v_source_6563_ = lean_array_fset(v_source_6557_, v_i_6556_, v___x_6562_);
                    v_target_6564_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_target_6558_, v_es_6561_);
                    v___x_6565_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6566_ = lean_nat_add(v_i_6556_, v___x_6565_);
                    crate::leanh::lean_dec(v_i_6556_);
                    v_i_6556_ = v___x_6566_;
                    v_source_6557_ = v_source_6563_;
                    v_target_6558_ = v_target_6564_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(
    mut v_data_6568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6569_ = lean_array_get_size(v_data_6568_);
    v___x_6570_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6571_ = lean_nat_mul(v___x_6569_, v___x_6570_);
    v___x_6572_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6573_ = crate::leanh::lean_box(0);
    v___x_6574_ = lean_mk_array(v_nbuckets_6571_, v___x_6573_);
    v___x_6575_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v___x_6572_, v_data_6568_, v___x_6574_);
    return v___x_6575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(
    mut v_a_6576_: *mut crate::leanh::LeanObject,
    mut v_x_6577_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6578_: u8 = 0;
    let mut v_key_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6577_) == 0 {
                    v___x_6578_ = 0;
                    return v___x_6578_;
                } else {
                    v_key_6579_ = crate::leanh::lean_ctor_get(v_x_6577_, 0);
                    v_tail_6580_ = crate::leanh::lean_ctor_get(v_x_6577_, 2);
                    v___x_6581_ = l_Lean_ExprStructEq_beq(v_key_6579_, v_a_6576_);
                    if v___x_6581_ == 0 {
                        v_x_6577_ = v_tail_6580_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg___boxed(
    mut v_a_6583_: *mut crate::leanh::LeanObject,
    mut v_x_6584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6585_: u8 = 0;
    let mut v_r_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_6583_, v_x_6584_);
    crate::leanh::lean_dec(v_x_6584_);
    crate::leanh::lean_dec_ref(v_a_6583_);
    v_r_6586_ = crate::leanh::lean_box((v_res_6585_) as usize);
    return v_r_6586_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(
    mut v_m_6587_: *mut crate::leanh::LeanObject,
    mut v_a_6588_: *mut crate::leanh::LeanObject,
    mut v_b_6589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6594_: u8 = 0;
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: u64 = 0;
    let mut v___x_6597_: u64 = 0;
    let mut v___x_6598_: u64 = 0;
    let mut v_fold_6599_: u64 = 0;
    let mut v___x_6600_: u64 = 0;
    let mut v___x_6601_: u64 = 0;
    let mut v___x_6602_: u64 = 0;
    let mut v___x_6603_: usize = 0;
    let mut v___x_6604_: usize = 0;
    let mut v___x_6605_: usize = 0;
    let mut v___x_6606_: usize = 0;
    let mut v___x_6607_: usize = 0;
    let mut v_bkt_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: u8 = 0;
    let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: u8 = 0;
    let mut v_val_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6590_ = crate::leanh::lean_ctor_get(v_m_6587_, 0);
                v_buckets_6591_ = crate::leanh::lean_ctor_get(v_m_6587_, 1);
                v_isSharedCheck_6634_ = (!crate::leanh::lean_is_exclusive(v_m_6587_)) as u8;
                if v_isSharedCheck_6634_ == 0 {
                    v___x_6593_ = v_m_6587_;
                    v_isShared_6594_ = v_isSharedCheck_6634_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_6591_);
                    crate::leanh::lean_inc(v_size_6590_);
                    crate::leanh::lean_dec(v_m_6587_);
                    v___x_6593_ = crate::leanh::lean_box(0);
                    v_isShared_6594_ = v_isSharedCheck_6634_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6595_ = lean_array_get_size(v_buckets_6591_);
                v___x_6596_ = l_Lean_ExprStructEq_hash(v_a_6588_);
                v___x_6597_ = 32u64;
                v___x_6598_ = lean_uint64_shift_right(v___x_6596_, v___x_6597_);
                v_fold_6599_ = lean_uint64_xor(v___x_6596_, v___x_6598_);
                v___x_6600_ = 16u64;
                v___x_6601_ = lean_uint64_shift_right(v_fold_6599_, v___x_6600_);
                v___x_6602_ = lean_uint64_xor(v_fold_6599_, v___x_6601_);
                v___x_6603_ = lean_uint64_to_usize(v___x_6602_);
                v___x_6604_ = lean_usize_of_nat(v___x_6595_);
                v___x_6605_ = 1usize;
                v___x_6606_ = lean_usize_sub(v___x_6604_, v___x_6605_);
                v___x_6607_ = lean_usize_land(v___x_6603_, v___x_6606_);
                v_bkt_6608_ = lean_array_uget_borrowed(v_buckets_6591_, v___x_6607_);
                v___x_6609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_6588_, v_bkt_6608_);
                if v___x_6609_ == 0 {
                    v___x_6610_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_6611_ = lean_nat_add(v_size_6590_, v___x_6610_);
                    crate::leanh::lean_dec(v_size_6590_);
                    crate::leanh::lean_inc(v_bkt_6608_);
                    v___x_6612_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6612_, 0, v_a_6588_);
                    crate::leanh::lean_ctor_set(v___x_6612_, 1, v_b_6589_);
                    crate::leanh::lean_ctor_set(v___x_6612_, 2, v_bkt_6608_);
                    v_buckets_x27_6613_ =
                        lean_array_uset(v_buckets_6591_, v___x_6607_, v___x_6612_);
                    v___x_6614_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_6615_ = lean_nat_mul(v_size_x27_6611_, v___x_6614_);
                    v___x_6616_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6617_ = lean_nat_div(v___x_6615_, v___x_6616_);
                    crate::leanh::lean_dec(v___x_6615_);
                    v___x_6618_ = lean_array_get_size(v_buckets_x27_6613_);
                    v___x_6619_ = lean_nat_dec_le(v___x_6617_, v___x_6618_);
                    crate::leanh::lean_dec(v___x_6617_);
                    if v___x_6619_ == 0 {
                        v_val_6620_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_buckets_x27_6613_);
                        if v_isShared_6594_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6593_, 1, v_val_6620_);
                            crate::leanh::lean_ctor_set(v___x_6593_, 0, v_size_x27_6611_);
                            v___x_6622_ = v___x_6593_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6623_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6623_,
                                0,
                                v_size_x27_6611_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6623_, 1, v_val_6620_);
                            v___x_6622_ = v_reuseFailAlloc_6623_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_6594_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6593_, 1, v_buckets_x27_6613_);
                            crate::leanh::lean_ctor_set(v___x_6593_, 0, v_size_x27_6611_);
                            v___x_6625_ = v___x_6593_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6626_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6626_,
                                0,
                                v_size_x27_6611_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6626_,
                                1,
                                v_buckets_x27_6613_,
                            );
                            v___x_6625_ = v_reuseFailAlloc_6626_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_6608_);
                    v___x_6627_ = crate::leanh::lean_box(0);
                    v_buckets_x27_6628_ =
                        lean_array_uset(v_buckets_6591_, v___x_6607_, v___x_6627_);
                    v___x_6629_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_6588_, v_b_6589_, v_bkt_6608_);
                    v___x_6630_ = lean_array_uset(v_buckets_x27_6628_, v___x_6607_, v___x_6629_);
                    if v_isShared_6594_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6593_, 1, v___x_6630_);
                        v___x_6632_ = v___x_6593_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_size_6590_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 1, v___x_6630_);
                        v___x_6632_ = v_reuseFailAlloc_6633_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6622_;
            }
            3 => {
                return v___x_6625_;
            }
            4 => {
                return v___x_6632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(
    mut v_a_6635_: *mut crate::leanh::LeanObject,
    mut v_e_6636_: *mut crate::leanh::LeanObject,
    mut v_a_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6639_ = lean_st_ref_take(v_a_6635_);
    v___x_6640_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v___x_6639_, v_e_6636_, v_a_6637_);
    v___x_6641_ = lean_st_ref_set(v_a_6635_, v___x_6640_);
    v___x_6642_ = crate::leanh::lean_box(0);
    return v___x_6642_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed(
    mut v_a_6643_: *mut crate::leanh::LeanObject,
    mut v_e_6644_: *mut crate::leanh::LeanObject,
    mut v_a_6645_: *mut crate::leanh::LeanObject,
    mut v___y_6646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6647_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2(v_a_6643_, v_e_6644_, v_a_6645_);
    crate::leanh::lean_dec(v_a_6643_);
    return v_res_6647_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(
    mut v_00_u03b1_6648_: *mut crate::leanh::LeanObject,
    mut v_x_6649_: *mut crate::leanh::LeanObject,
    mut v___y_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6655_ = crate::leanh::lean_apply_1(v_x_6649_, crate::leanh::lean_box(0));
    v___x_6656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6656_, 0, v___x_6655_);
    return v___x_6656_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0___boxed(
    mut v_00_u03b1_6657_: *mut crate::leanh::LeanObject,
    mut v_x_6658_: *mut crate::leanh::LeanObject,
    mut v___y_6659_: *mut crate::leanh::LeanObject,
    mut v___y_6660_: *mut crate::leanh::LeanObject,
    mut v___y_6661_: *mut crate::leanh::LeanObject,
    mut v___y_6662_: *mut crate::leanh::LeanObject,
    mut v___y_6663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(v_00_u03b1_6657_, v_x_6658_, v___y_6659_, v___y_6660_, v___y_6661_, v___y_6662_);
    crate::leanh::lean_dec(v___y_6662_);
    crate::leanh::lean_dec_ref(v___y_6661_);
    crate::leanh::lean_dec(v___y_6660_);
    crate::leanh::lean_dec_ref(v___y_6659_);
    return v_res_6664_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(
    mut v_a_6665_: *mut crate::leanh::LeanObject,
    mut v_x_6666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: u8 = 0;
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6666_) == 0 {
                    v___x_6667_ = crate::leanh::lean_box(0);
                    return v___x_6667_;
                } else {
                    v_key_6668_ = crate::leanh::lean_ctor_get(v_x_6666_, 0);
                    v_value_6669_ = crate::leanh::lean_ctor_get(v_x_6666_, 1);
                    v_tail_6670_ = crate::leanh::lean_ctor_get(v_x_6666_, 2);
                    v___x_6671_ = l_Lean_ExprStructEq_beq(v_key_6668_, v_a_6665_);
                    if v___x_6671_ == 0 {
                        v_x_6666_ = v_tail_6670_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6669_);
                        v___x_6673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6673_, 0, v_value_6669_);
                        return v___x_6673_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg___boxed(
    mut v_a_6674_: *mut crate::leanh::LeanObject,
    mut v_x_6675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_6674_, v_x_6675_);
    crate::leanh::lean_dec(v_x_6675_);
    crate::leanh::lean_dec_ref(v_a_6674_);
    return v_res_6676_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(
    mut v_m_6677_: *mut crate::leanh::LeanObject,
    mut v_a_6678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: u64 = 0;
    let mut v___x_6682_: u64 = 0;
    let mut v___x_6683_: u64 = 0;
    let mut v_fold_6684_: u64 = 0;
    let mut v___x_6685_: u64 = 0;
    let mut v___x_6686_: u64 = 0;
    let mut v___x_6687_: u64 = 0;
    let mut v___x_6688_: usize = 0;
    let mut v___x_6689_: usize = 0;
    let mut v___x_6690_: usize = 0;
    let mut v___x_6691_: usize = 0;
    let mut v___x_6692_: usize = 0;
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_6679_ = crate::leanh::lean_ctor_get(v_m_6677_, 1);
    v___x_6680_ = lean_array_get_size(v_buckets_6679_);
    v___x_6681_ = l_Lean_ExprStructEq_hash(v_a_6678_);
    v___x_6682_ = 32u64;
    v___x_6683_ = lean_uint64_shift_right(v___x_6681_, v___x_6682_);
    v_fold_6684_ = lean_uint64_xor(v___x_6681_, v___x_6683_);
    v___x_6685_ = 16u64;
    v___x_6686_ = lean_uint64_shift_right(v_fold_6684_, v___x_6685_);
    v___x_6687_ = lean_uint64_xor(v_fold_6684_, v___x_6686_);
    v___x_6688_ = lean_uint64_to_usize(v___x_6687_);
    v___x_6689_ = lean_usize_of_nat(v___x_6680_);
    v___x_6690_ = 1usize;
    v___x_6691_ = lean_usize_sub(v___x_6689_, v___x_6690_);
    v___x_6692_ = lean_usize_land(v___x_6688_, v___x_6691_);
    v___x_6693_ = lean_array_uget_borrowed(v_buckets_6679_, v___x_6692_);
    v___x_6694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_6678_, v___x_6693_);
    return v___x_6694_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg___boxed(
    mut v_m_6695_: *mut crate::leanh::LeanObject,
    mut v_a_6696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_6695_, v_a_6696_);
    crate::leanh::lean_dec_ref(v_a_6696_);
    crate::leanh::lean_dec_ref(v_m_6695_);
    return v_res_6697_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(
    mut v_k_6698_: *mut crate::leanh::LeanObject,
    mut v___y_6699_: *mut crate::leanh::LeanObject,
    mut v_b_6700_: *mut crate::leanh::LeanObject,
    mut v___y_6701_: *mut crate::leanh::LeanObject,
    mut v___y_6702_: *mut crate::leanh::LeanObject,
    mut v___y_6703_: *mut crate::leanh::LeanObject,
    mut v___y_6704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_6704_);
    crate::leanh::lean_inc_ref(v___y_6703_);
    crate::leanh::lean_inc(v___y_6702_);
    crate::leanh::lean_inc_ref(v___y_6701_);
    crate::leanh::lean_inc(v___y_6699_);
    v___x_6706_ = crate::leanh::lean_apply_7(
        v_k_6698_,
        v_b_6700_,
        v___y_6699_,
        v___y_6701_,
        v___y_6702_,
        v___y_6703_,
        v___y_6704_,
        crate::leanh::lean_box(0),
    );
    return v___x_6706_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed(
    mut v_k_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
    mut v_b_6709_: *mut crate::leanh::LeanObject,
    mut v___y_6710_: *mut crate::leanh::LeanObject,
    mut v___y_6711_: *mut crate::leanh::LeanObject,
    mut v___y_6712_: *mut crate::leanh::LeanObject,
    mut v___y_6713_: *mut crate::leanh::LeanObject,
    mut v___y_6714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6715_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0(v_k_6707_, v___y_6708_, v_b_6709_, v___y_6710_, v___y_6711_, v___y_6712_, v___y_6713_);
    crate::leanh::lean_dec(v___y_6713_);
    crate::leanh::lean_dec_ref(v___y_6712_);
    crate::leanh::lean_dec(v___y_6711_);
    crate::leanh::lean_dec_ref(v___y_6710_);
    crate::leanh::lean_dec(v___y_6708_);
    return v_res_6715_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(
    mut v_name_6716_: *mut crate::leanh::LeanObject,
    mut v_bi_6717_: u8,
    mut v_type_6718_: *mut crate::leanh::LeanObject,
    mut v_k_6719_: *mut crate::leanh::LeanObject,
    mut v_kind_6720_: u8,
    mut v___y_6721_: *mut crate::leanh::LeanObject,
    mut v___y_6722_: *mut crate::leanh::LeanObject,
    mut v___y_6723_: *mut crate::leanh::LeanObject,
    mut v___y_6724_: *mut crate::leanh::LeanObject,
    mut v___y_6725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6732_: u8 = 0;
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6721_);
                v___f_6727_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_6727_, 0, v_k_6719_);
                crate::leanh::lean_closure_set(v___f_6727_, 1, v___y_6721_);
                v___x_6728_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_6716_,
                    v_bi_6717_,
                    v_type_6718_,
                    v___f_6727_,
                    v_kind_6720_,
                    v___y_6722_,
                    v___y_6723_,
                    v___y_6724_,
                    v___y_6725_,
                );
                if crate::leanh::lean_obj_tag(v___x_6728_) == 0 {
                    return v___x_6728_;
                } else {
                    v_a_6729_ = crate::leanh::lean_ctor_get(v___x_6728_, 0);
                    v_isSharedCheck_6736_ = (!crate::leanh::lean_is_exclusive(v___x_6728_)) as u8;
                    if v_isSharedCheck_6736_ == 0 {
                        v___x_6731_ = v___x_6728_;
                        v_isShared_6732_ = v_isSharedCheck_6736_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6729_);
                        crate::leanh::lean_dec(v___x_6728_);
                        v___x_6731_ = crate::leanh::lean_box(0);
                        v_isShared_6732_ = v_isSharedCheck_6736_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6732_ == 0 {
                    v___x_6734_ = v___x_6731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6735_, 0, v_a_6729_);
                    v___x_6734_ = v_reuseFailAlloc_6735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___boxed(
    mut v_name_6737_: *mut crate::leanh::LeanObject,
    mut v_bi_6738_: *mut crate::leanh::LeanObject,
    mut v_type_6739_: *mut crate::leanh::LeanObject,
    mut v_k_6740_: *mut crate::leanh::LeanObject,
    mut v_kind_6741_: *mut crate::leanh::LeanObject,
    mut v___y_6742_: *mut crate::leanh::LeanObject,
    mut v___y_6743_: *mut crate::leanh::LeanObject,
    mut v___y_6744_: *mut crate::leanh::LeanObject,
    mut v___y_6745_: *mut crate::leanh::LeanObject,
    mut v___y_6746_: *mut crate::leanh::LeanObject,
    mut v___y_6747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_6748_: u8 = 0;
    let mut v_kind_boxed_6749_: u8 = 0;
    let mut v_res_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_6748_ = (crate::leanh::lean_unbox(v_bi_6738_) as u8);
    v_kind_boxed_6749_ = (crate::leanh::lean_unbox(v_kind_6741_) as u8);
    v_res_6750_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_6737_, v_bi_boxed_6748_, v_type_6739_, v_k_6740_, v_kind_boxed_6749_, v___y_6742_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
    crate::leanh::lean_dec(v___y_6746_);
    crate::leanh::lean_dec_ref(v___y_6745_);
    crate::leanh::lean_dec(v___y_6744_);
    crate::leanh::lean_dec_ref(v___y_6743_);
    crate::leanh::lean_dec(v___y_6742_);
    return v_res_6750_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(
    mut v___x_6751_: *mut crate::leanh::LeanObject,
    mut v___y_6752_: *mut crate::leanh::LeanObject,
    mut v___y_6753_: *mut crate::leanh::LeanObject,
    mut v___y_6754_: *mut crate::leanh::LeanObject,
    mut v___y_6755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6757_, 0, v___x_6751_);
    return v___x_6757_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed(
    mut v___x_6758_: *mut crate::leanh::LeanObject,
    mut v___y_6759_: *mut crate::leanh::LeanObject,
    mut v___y_6760_: *mut crate::leanh::LeanObject,
    mut v___y_6761_: *mut crate::leanh::LeanObject,
    mut v___y_6762_: *mut crate::leanh::LeanObject,
    mut v___y_6763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6764_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2(v___x_6758_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
    crate::leanh::lean_dec(v___y_6762_);
    crate::leanh::lean_dec_ref(v___y_6761_);
    crate::leanh::lean_dec(v___y_6760_);
    crate::leanh::lean_dec_ref(v___y_6759_);
    return v_res_6764_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(
    mut v_name_6765_: *mut crate::leanh::LeanObject,
    mut v_type_6766_: *mut crate::leanh::LeanObject,
    mut v_val_6767_: *mut crate::leanh::LeanObject,
    mut v_k_6768_: *mut crate::leanh::LeanObject,
    mut v_nondep_6769_: u8,
    mut v_kind_6770_: u8,
    mut v___y_6771_: *mut crate::leanh::LeanObject,
    mut v___y_6772_: *mut crate::leanh::LeanObject,
    mut v___y_6773_: *mut crate::leanh::LeanObject,
    mut v___y_6774_: *mut crate::leanh::LeanObject,
    mut v___y_6775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6771_);
                v___f_6777_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_6777_, 0, v_k_6768_);
                crate::leanh::lean_closure_set(v___f_6777_, 1, v___y_6771_);
                v___x_6778_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_6765_,
                    v_type_6766_,
                    v_val_6767_,
                    v___f_6777_,
                    v_nondep_6769_,
                    v_kind_6770_,
                    v___y_6772_,
                    v___y_6773_,
                    v___y_6774_,
                    v___y_6775_,
                );
                if crate::leanh::lean_obj_tag(v___x_6778_) == 0 {
                    return v___x_6778_;
                } else {
                    v_a_6779_ = crate::leanh::lean_ctor_get(v___x_6778_, 0);
                    v_isSharedCheck_6786_ = (!crate::leanh::lean_is_exclusive(v___x_6778_)) as u8;
                    if v_isSharedCheck_6786_ == 0 {
                        v___x_6781_ = v___x_6778_;
                        v_isShared_6782_ = v_isSharedCheck_6786_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6779_);
                        crate::leanh::lean_dec(v___x_6778_);
                        v___x_6781_ = crate::leanh::lean_box(0);
                        v_isShared_6782_ = v_isSharedCheck_6786_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6782_ == 0 {
                    v___x_6784_ = v___x_6781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6785_, 0, v_a_6779_);
                    v___x_6784_ = v_reuseFailAlloc_6785_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg___boxed(
    mut v_name_6787_: *mut crate::leanh::LeanObject,
    mut v_type_6788_: *mut crate::leanh::LeanObject,
    mut v_val_6789_: *mut crate::leanh::LeanObject,
    mut v_k_6790_: *mut crate::leanh::LeanObject,
    mut v_nondep_6791_: *mut crate::leanh::LeanObject,
    mut v_kind_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
    mut v___y_6794_: *mut crate::leanh::LeanObject,
    mut v___y_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
    mut v___y_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_6799_: u8 = 0;
    let mut v_kind_boxed_6800_: u8 = 0;
    let mut v_res_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_6799_ = (crate::leanh::lean_unbox(v_nondep_6791_) as u8);
    v_kind_boxed_6800_ = (crate::leanh::lean_unbox(v_kind_6792_) as u8);
    v_res_6801_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_6787_, v_type_6788_, v_val_6789_, v_k_6790_, v_nondep_boxed_6799_, v_kind_boxed_6800_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_);
    crate::leanh::lean_dec(v___y_6797_);
    crate::leanh::lean_dec_ref(v___y_6796_);
    crate::leanh::lean_dec(v___y_6795_);
    crate::leanh::lean_dec_ref(v___y_6794_);
    crate::leanh::lean_dec(v___y_6793_);
    return v_res_6801_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6807_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6808_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6808_, 0, v___x_6807_);
    return v___x_6808_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__3);
    v___x_6810_ = l_Lean_MessageData_ofFormat(v___x_6809_);
    return v___x_6810_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6811_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__4);
    v___x_6812_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__2;
    v___x_6813_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6813_, 0, v___x_6812_);
    crate::leanh::lean_ctor_set(v___x_6813_, 1, v___x_6811_);
    return v___x_6813_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(
    mut v_ref_6814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___closed__5);
    v___x_6817_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6817_, 0, v_ref_6814_);
    crate::leanh::lean_ctor_set(v___x_6817_, 1, v___x_6816_);
    v___x_6818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6818_, 0, v___x_6817_);
    return v___x_6818_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg___boxed(
    mut v_ref_6819_: *mut crate::leanh::LeanObject,
    mut v___y_6820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6821_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_6819_);
    return v_res_6821_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(
    mut v_x_6822_: *mut crate::leanh::LeanObject,
    mut v___y_6823_: *mut crate::leanh::LeanObject,
    mut v___y_6824_: *mut crate::leanh::LeanObject,
    mut v___y_6825_: *mut crate::leanh::LeanObject,
    mut v___y_6826_: *mut crate::leanh::LeanObject,
    mut v___y_6827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6834_: u8 = 0;
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6838_: u8 = 0;
    let mut v_fileName_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6851_: u8 = 0;
    let mut v_cancelTk_x3f_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6853_: u8 = 0;
    let mut v_inheritedTraceOptions_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: u8 = 0;
    let mut v___x_6862_: u8 = 0;
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6839_ = crate::leanh::lean_ctor_get(v___y_6826_, 0);
                v_fileMap_6840_ = crate::leanh::lean_ctor_get(v___y_6826_, 1);
                v_options_6841_ = crate::leanh::lean_ctor_get(v___y_6826_, 2);
                v_currRecDepth_6842_ = crate::leanh::lean_ctor_get(v___y_6826_, 3);
                v_maxRecDepth_6843_ = crate::leanh::lean_ctor_get(v___y_6826_, 4);
                v_ref_6844_ = crate::leanh::lean_ctor_get(v___y_6826_, 5);
                v_currNamespace_6845_ = crate::leanh::lean_ctor_get(v___y_6826_, 6);
                v_openDecls_6846_ = crate::leanh::lean_ctor_get(v___y_6826_, 7);
                v_initHeartbeats_6847_ = crate::leanh::lean_ctor_get(v___y_6826_, 8);
                v_maxHeartbeats_6848_ = crate::leanh::lean_ctor_get(v___y_6826_, 9);
                v_quotContext_6849_ = crate::leanh::lean_ctor_get(v___y_6826_, 10);
                v_currMacroScope_6850_ = crate::leanh::lean_ctor_get(v___y_6826_, 11);
                v_diag_6851_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6826_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6852_ = crate::leanh::lean_ctor_get(v___y_6826_, 12);
                v_suppressElabErrors_6853_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6826_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6854_ = crate::leanh::lean_ctor_get(v___y_6826_, 13);
                v___x_6860_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6861_ = lean_nat_dec_eq(v_maxRecDepth_6843_, v___x_6860_);
                if v___x_6861_ == 0 {
                    v___x_6862_ = lean_nat_dec_eq(v_currRecDepth_6842_, v_maxRecDepth_6843_);
                    if v___x_6862_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_6822_);
                        crate::leanh::lean_inc(v_ref_6844_);
                        v___x_6863_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_6844_);
                        v___y_6830_ = v___x_6863_;
                        state = 1;
                        continue;
                    }
                } else {
                    state = 4;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_6830_) == 0 {
                    return v___y_6830_;
                } else {
                    v_a_6831_ = crate::leanh::lean_ctor_get(v___y_6830_, 0);
                    v_isSharedCheck_6838_ = (!crate::leanh::lean_is_exclusive(v___y_6830_)) as u8;
                    if v_isSharedCheck_6838_ == 0 {
                        v___x_6833_ = v___y_6830_;
                        v_isShared_6834_ = v_isSharedCheck_6838_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6831_);
                        crate::leanh::lean_dec(v___y_6830_);
                        v___x_6833_ = crate::leanh::lean_box(0);
                        v_isShared_6834_ = v_isSharedCheck_6838_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6834_ == 0 {
                    v___x_6836_ = v___x_6833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6837_, 0, v_a_6831_);
                    v___x_6836_ = v_reuseFailAlloc_6837_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6836_;
            }
            4 => {
                v___x_6856_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6857_ = lean_nat_add(v_currRecDepth_6842_, v___x_6856_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6854_);
                crate::leanh::lean_inc(v_cancelTk_x3f_6852_);
                crate::leanh::lean_inc(v_currMacroScope_6850_);
                crate::leanh::lean_inc(v_quotContext_6849_);
                crate::leanh::lean_inc(v_maxHeartbeats_6848_);
                crate::leanh::lean_inc(v_initHeartbeats_6847_);
                crate::leanh::lean_inc(v_openDecls_6846_);
                crate::leanh::lean_inc(v_currNamespace_6845_);
                crate::leanh::lean_inc(v_ref_6844_);
                crate::leanh::lean_inc(v_maxRecDepth_6843_);
                crate::leanh::lean_inc_ref(v_options_6841_);
                crate::leanh::lean_inc_ref(v_fileMap_6840_);
                crate::leanh::lean_inc_ref(v_fileName_6839_);
                v___x_6858_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_6858_, 0, v_fileName_6839_);
                crate::leanh::lean_ctor_set(v___x_6858_, 1, v_fileMap_6840_);
                crate::leanh::lean_ctor_set(v___x_6858_, 2, v_options_6841_);
                crate::leanh::lean_ctor_set(v___x_6858_, 3, v___x_6857_);
                crate::leanh::lean_ctor_set(v___x_6858_, 4, v_maxRecDepth_6843_);
                crate::leanh::lean_ctor_set(v___x_6858_, 5, v_ref_6844_);
                crate::leanh::lean_ctor_set(v___x_6858_, 6, v_currNamespace_6845_);
                crate::leanh::lean_ctor_set(v___x_6858_, 7, v_openDecls_6846_);
                crate::leanh::lean_ctor_set(v___x_6858_, 8, v_initHeartbeats_6847_);
                crate::leanh::lean_ctor_set(v___x_6858_, 9, v_maxHeartbeats_6848_);
                crate::leanh::lean_ctor_set(v___x_6858_, 10, v_quotContext_6849_);
                crate::leanh::lean_ctor_set(v___x_6858_, 11, v_currMacroScope_6850_);
                crate::leanh::lean_ctor_set(v___x_6858_, 12, v_cancelTk_x3f_6852_);
                crate::leanh::lean_ctor_set(v___x_6858_, 13, v_inheritedTraceOptions_6854_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6858_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_6851_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6858_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6853_,
                );
                crate::leanh::lean_inc(v___y_6827_);
                crate::leanh::lean_inc(v___y_6825_);
                crate::leanh::lean_inc_ref(v___y_6824_);
                crate::leanh::lean_inc(v___y_6823_);
                v___x_6859_ = crate::leanh::lean_apply_6(
                    v_x_6822_,
                    v___y_6823_,
                    v___y_6824_,
                    v___y_6825_,
                    v___x_6858_,
                    v___y_6827_,
                    crate::leanh::lean_box(0),
                );
                v___y_6830_ = v___x_6859_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg___boxed(
    mut v_x_6864_: *mut crate::leanh::LeanObject,
    mut v___y_6865_: *mut crate::leanh::LeanObject,
    mut v___y_6866_: *mut crate::leanh::LeanObject,
    mut v___y_6867_: *mut crate::leanh::LeanObject,
    mut v___y_6868_: *mut crate::leanh::LeanObject,
    mut v___y_6869_: *mut crate::leanh::LeanObject,
    mut v___y_6870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6871_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_);
    crate::leanh::lean_dec(v___y_6869_);
    crate::leanh::lean_dec_ref(v___y_6868_);
    crate::leanh::lean_dec(v___y_6867_);
    crate::leanh::lean_dec_ref(v___y_6866_);
    crate::leanh::lean_dec(v___y_6865_);
    return v_res_6871_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(
    mut v_fvars_6875_: *mut crate::leanh::LeanObject,
    mut v_pre_6876_: *mut crate::leanh::LeanObject,
    mut v_post_6877_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6878_: u8,
    mut v_skipConstInApp_6879_: u8,
    mut v_skipInstances_6880_: u8,
    mut v_body_6881_: *mut crate::leanh::LeanObject,
    mut v_x_6882_: *mut crate::leanh::LeanObject,
    mut v___y_6883_: *mut crate::leanh::LeanObject,
    mut v___y_6884_: *mut crate::leanh::LeanObject,
    mut v___y_6885_: *mut crate::leanh::LeanObject,
    mut v___y_6886_: *mut crate::leanh::LeanObject,
    mut v___y_6887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6889_ = lean_array_push(v_fvars_6875_, v_x_6882_);
    v___x_6890_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_6876_, v_post_6877_, v_usedLetOnly_6878_, v_skipConstInApp_6879_, v_skipInstances_6880_, v___x_6889_, v_body_6881_, v___y_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_);
    return v___x_6890_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed(
    mut v_fvars_6891_: *mut crate::leanh::LeanObject,
    mut v_pre_6892_: *mut crate::leanh::LeanObject,
    mut v_post_6893_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6894_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_6895_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_6896_: *mut crate::leanh::LeanObject,
    mut v_body_6897_: *mut crate::leanh::LeanObject,
    mut v_x_6898_: *mut crate::leanh::LeanObject,
    mut v___y_6899_: *mut crate::leanh::LeanObject,
    mut v___y_6900_: *mut crate::leanh::LeanObject,
    mut v___y_6901_: *mut crate::leanh::LeanObject,
    mut v___y_6902_: *mut crate::leanh::LeanObject,
    mut v___y_6903_: *mut crate::leanh::LeanObject,
    mut v___y_6904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_6905_: u8 = 0;
    let mut v_skipConstInApp_boxed_6906_: u8 = 0;
    let mut v_skipInstances_boxed_6907_: u8 = 0;
    let mut v_res_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_6905_ = (crate::leanh::lean_unbox(v_usedLetOnly_6894_) as u8);
    v_skipConstInApp_boxed_6906_ = (crate::leanh::lean_unbox(v_skipConstInApp_6895_) as u8);
    v_skipInstances_boxed_6907_ = (crate::leanh::lean_unbox(v_skipInstances_6896_) as u8);
    v_res_6908_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0(v_fvars_6891_, v_pre_6892_, v_post_6893_, v_usedLetOnly_boxed_6905_, v_skipConstInApp_boxed_6906_, v_skipInstances_boxed_6907_, v_body_6897_, v_x_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_);
    crate::leanh::lean_dec(v___y_6903_);
    crate::leanh::lean_dec_ref(v___y_6902_);
    crate::leanh::lean_dec(v___y_6901_);
    crate::leanh::lean_dec_ref(v___y_6900_);
    crate::leanh::lean_dec(v___y_6899_);
    return v_res_6908_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(
    mut v_pre_6909_: *mut crate::leanh::LeanObject,
    mut v_post_6910_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6911_: u8,
    mut v_skipConstInApp_6912_: u8,
    mut v_skipInstances_6913_: u8,
    mut v_e_6914_: *mut crate::leanh::LeanObject,
    mut v_a_6915_: *mut crate::leanh::LeanObject,
    mut v___y_6916_: *mut crate::leanh::LeanObject,
    mut v___y_6917_: *mut crate::leanh::LeanObject,
    mut v___y_6918_: *mut crate::leanh::LeanObject,
    mut v___y_6919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6925_: u8 = 0;
    let mut v_e_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6940_: u8 = 0;
    let mut v_a_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6944_: u8 = 0;
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_post_6910_);
                crate::leanh::lean_inc(v___y_6919_);
                crate::leanh::lean_inc_ref(v___y_6918_);
                crate::leanh::lean_inc(v___y_6917_);
                crate::leanh::lean_inc_ref(v___y_6916_);
                crate::leanh::lean_inc_ref(v_e_6914_);
                v___x_6921_ = crate::leanh::lean_apply_6(
                    v_post_6910_,
                    v_e_6914_,
                    v___y_6916_,
                    v___y_6917_,
                    v___y_6918_,
                    v___y_6919_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6921_) == 0 {
                    v_a_6922_ = crate::leanh::lean_ctor_get(v___x_6921_, 0);
                    v_isSharedCheck_6940_ = (!crate::leanh::lean_is_exclusive(v___x_6921_)) as u8;
                    if v_isSharedCheck_6940_ == 0 {
                        v___x_6924_ = v___x_6921_;
                        v_isShared_6925_ = v_isSharedCheck_6940_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6922_);
                        crate::leanh::lean_dec(v___x_6921_);
                        v___x_6924_ = crate::leanh::lean_box(0);
                        v_isShared_6925_ = v_isSharedCheck_6940_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6914_);
                    crate::leanh::lean_dec_ref(v_post_6910_);
                    crate::leanh::lean_dec_ref(v_pre_6909_);
                    v_a_6941_ = crate::leanh::lean_ctor_get(v___x_6921_, 0);
                    v_isSharedCheck_6948_ = (!crate::leanh::lean_is_exclusive(v___x_6921_)) as u8;
                    if v_isSharedCheck_6948_ == 0 {
                        v___x_6943_ = v___x_6921_;
                        v_isShared_6944_ = v_isSharedCheck_6948_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6941_);
                        crate::leanh::lean_dec(v___x_6921_);
                        v___x_6943_ = crate::leanh::lean_box(0);
                        v_isShared_6944_ = v_isSharedCheck_6948_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_6922_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_e_6914_);
                    crate::leanh::lean_dec_ref(v_post_6910_);
                    crate::leanh::lean_dec_ref(v_pre_6909_);
                    v_e_6926_ = crate::leanh::lean_ctor_get(v_a_6922_, 0);
                    crate::leanh::lean_inc_ref(v_e_6926_);
                    crate::leanh::lean_dec_ref_known(v_a_6922_, 1);
                    if v_isShared_6925_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6924_, 0, v_e_6926_);
                        v___x_6928_ = v___x_6924_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_e_6926_);
                        v___x_6928_ = v_reuseFailAlloc_6929_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_6924_);
                    crate::leanh::lean_dec_ref(v_e_6914_);
                    v_e_6930_ = crate::leanh::lean_ctor_get(v_a_6922_, 0);
                    crate::leanh::lean_inc_ref(v_e_6930_);
                    crate::leanh::lean_dec_ref_known(v_a_6922_, 1);
                    v___x_6931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_6909_, v_post_6910_, v_usedLetOnly_6911_, v_skipConstInApp_6912_, v_skipInstances_6913_, v_e_6930_, v_a_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_);
                    return v___x_6931_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_post_6910_);
                    crate::leanh::lean_dec_ref(v_pre_6909_);
                    v_e_x3f_6932_ = crate::leanh::lean_ctor_get(v_a_6922_, 0);
                    crate::leanh::lean_inc(v_e_x3f_6932_);
                    crate::leanh::lean_dec_ref_known(v_a_6922_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_6932_) == 0 {
                        if v_isShared_6925_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6924_, 0, v_e_6914_);
                            v___x_6934_ = v___x_6924_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6935_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_e_6914_);
                            v___x_6934_ = v_reuseFailAlloc_6935_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6914_);
                        v_val_6936_ = crate::leanh::lean_ctor_get(v_e_x3f_6932_, 0);
                        crate::leanh::lean_inc(v_val_6936_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_6932_, 1);
                        if v_isShared_6925_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6924_, 0, v_val_6936_);
                            v___x_6938_ = v___x_6924_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6939_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6939_, 0, v_val_6936_);
                            v___x_6938_ = v_reuseFailAlloc_6939_;
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            2 => {
                return v___x_6928_;
            }
            3 => {
                return v___x_6934_;
            }
            4 => {
                return v___x_6938_;
            }
            5 => {
                if v_isShared_6944_ == 0 {
                    v___x_6946_ = v___x_6943_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6947_, 0, v_a_6941_);
                    v___x_6946_ = v_reuseFailAlloc_6947_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(
    mut v_pre_6949_: *mut crate::leanh::LeanObject,
    mut v_post_6950_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6951_: u8,
    mut v_skipConstInApp_6952_: u8,
    mut v_skipInstances_6953_: u8,
    mut v_fvars_6954_: *mut crate::leanh::LeanObject,
    mut v_e_6955_: *mut crate::leanh::LeanObject,
    mut v_a_6956_: *mut crate::leanh::LeanObject,
    mut v___y_6957_: *mut crate::leanh::LeanObject,
    mut v___y_6958_: *mut crate::leanh::LeanObject,
    mut v___y_6959_: *mut crate::leanh::LeanObject,
    mut v___y_6960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_6955_) == 6 {
        let mut v_binderName_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_6965_: u8 = 0;
        let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_6962_ = crate::leanh::lean_ctor_get(v_e_6955_, 0);
        crate::leanh::lean_inc(v_binderName_6962_);
        v_binderType_6963_ = crate::leanh::lean_ctor_get(v_e_6955_, 1);
        crate::leanh::lean_inc_ref(v_binderType_6963_);
        v_body_6964_ = crate::leanh::lean_ctor_get(v_e_6955_, 2);
        crate::leanh::lean_inc_ref(v_body_6964_);
        v_binderInfo_6965_ = crate::leanh::lean_ctor_get_uint8(
            v_e_6955_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_6955_, 3);
        v___x_6966_ = lean_expr_instantiate_rev(v_binderType_6963_, v_fvars_6954_);
        crate::leanh::lean_dec_ref(v_binderType_6963_);
        crate::leanh::lean_inc_ref(v_post_6950_);
        crate::leanh::lean_inc_ref(v_pre_6949_);
        v___x_6967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_6949_, v_post_6950_, v_usedLetOnly_6951_, v_skipConstInApp_6952_, v_skipInstances_6953_, v___x_6966_, v_a_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
        if crate::leanh::lean_obj_tag(v___x_6967_) == 0 {
            let mut v_a_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6973_: u8 = 0;
            let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6968_ = crate::leanh::lean_ctor_get(v___x_6967_, 0);
            crate::leanh::lean_inc(v_a_6968_);
            crate::leanh::lean_dec_ref_known(v___x_6967_, 1);
            v___x_6969_ = crate::leanh::lean_box((v_usedLetOnly_6951_) as usize);
            v___x_6970_ = crate::leanh::lean_box((v_skipConstInApp_6952_) as usize);
            v___x_6971_ = crate::leanh::lean_box((v_skipInstances_6953_) as usize);
            v___f_6972_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            crate::leanh::lean_closure_set(v___f_6972_, 0, v_fvars_6954_);
            crate::leanh::lean_closure_set(v___f_6972_, 1, v_pre_6949_);
            crate::leanh::lean_closure_set(v___f_6972_, 2, v_post_6950_);
            crate::leanh::lean_closure_set(v___f_6972_, 3, v___x_6969_);
            crate::leanh::lean_closure_set(v___f_6972_, 4, v___x_6970_);
            crate::leanh::lean_closure_set(v___f_6972_, 5, v___x_6971_);
            crate::leanh::lean_closure_set(v___f_6972_, 6, v_body_6964_);
            v___x_6973_ = 0;
            v___x_6974_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_6962_, v_binderInfo_6965_, v_a_6968_, v___f_6972_, v___x_6973_, v_a_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
            return v___x_6974_;
        } else {
            crate::leanh::lean_dec_ref(v_body_6964_);
            crate::leanh::lean_dec(v_binderName_6962_);
            crate::leanh::lean_dec_ref(v_fvars_6954_);
            crate::leanh::lean_dec_ref(v_post_6950_);
            crate::leanh::lean_dec_ref(v_pre_6949_);
            return v___x_6967_;
        }
    } else {
        let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6975_ = lean_expr_instantiate_rev(v_e_6955_, v_fvars_6954_);
        crate::leanh::lean_dec_ref(v_e_6955_);
        crate::leanh::lean_inc_ref(v_post_6950_);
        crate::leanh::lean_inc_ref(v_pre_6949_);
        v___x_6976_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_6949_, v_post_6950_, v_usedLetOnly_6951_, v_skipConstInApp_6952_, v_skipInstances_6953_, v___x_6975_, v_a_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
        if crate::leanh::lean_obj_tag(v___x_6976_) == 0 {
            let mut v_a_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6978_: u8 = 0;
            let mut v___x_6979_: u8 = 0;
            let mut v___x_6980_: u8 = 0;
            let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6977_ = crate::leanh::lean_ctor_get(v___x_6976_, 0);
            crate::leanh::lean_inc(v_a_6977_);
            crate::leanh::lean_dec_ref_known(v___x_6976_, 1);
            v___x_6978_ = 0;
            v___x_6979_ = 1;
            v___x_6980_ = 1;
            v___x_6981_ = l_Lean_Meta_mkLambdaFVars(
                v_fvars_6954_,
                v_a_6977_,
                v___x_6978_,
                v_usedLetOnly_6951_,
                v___x_6978_,
                v___x_6979_,
                v___x_6980_,
                v___y_6957_,
                v___y_6958_,
                v___y_6959_,
                v___y_6960_,
            );
            crate::leanh::lean_dec_ref(v_fvars_6954_);
            if crate::leanh::lean_obj_tag(v___x_6981_) == 0 {
                let mut v_a_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_6982_ = crate::leanh::lean_ctor_get(v___x_6981_, 0);
                crate::leanh::lean_inc(v_a_6982_);
                crate::leanh::lean_dec_ref_known(v___x_6981_, 1);
                v___x_6983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_6949_, v_post_6950_, v_usedLetOnly_6951_, v_skipConstInApp_6952_, v_skipInstances_6953_, v_a_6982_, v_a_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
                return v___x_6983_;
            } else {
                crate::leanh::lean_dec_ref(v_post_6950_);
                crate::leanh::lean_dec_ref(v_pre_6949_);
                return v___x_6981_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_6954_);
            crate::leanh::lean_dec_ref(v_post_6950_);
            crate::leanh::lean_dec_ref(v_pre_6949_);
            return v___x_6976_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(
    mut v_fvars_6984_: *mut crate::leanh::LeanObject,
    mut v_pre_6985_: *mut crate::leanh::LeanObject,
    mut v_post_6986_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_6987_: u8,
    mut v_skipConstInApp_6988_: u8,
    mut v_skipInstances_6989_: u8,
    mut v_body_6990_: *mut crate::leanh::LeanObject,
    mut v_x_6991_: *mut crate::leanh::LeanObject,
    mut v___y_6992_: *mut crate::leanh::LeanObject,
    mut v___y_6993_: *mut crate::leanh::LeanObject,
    mut v___y_6994_: *mut crate::leanh::LeanObject,
    mut v___y_6995_: *mut crate::leanh::LeanObject,
    mut v___y_6996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6998_ = lean_array_push(v_fvars_6984_, v_x_6991_);
    v___x_6999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_6985_, v_post_6986_, v_usedLetOnly_6987_, v_skipConstInApp_6988_, v_skipInstances_6989_, v___x_6998_, v_body_6990_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_, v___y_6996_);
    return v___x_6999_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed(
    mut v_fvars_7000_: *mut crate::leanh::LeanObject,
    mut v_pre_7001_: *mut crate::leanh::LeanObject,
    mut v_post_7002_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7003_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7004_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7005_: *mut crate::leanh::LeanObject,
    mut v_body_7006_: *mut crate::leanh::LeanObject,
    mut v_x_7007_: *mut crate::leanh::LeanObject,
    mut v___y_7008_: *mut crate::leanh::LeanObject,
    mut v___y_7009_: *mut crate::leanh::LeanObject,
    mut v___y_7010_: *mut crate::leanh::LeanObject,
    mut v___y_7011_: *mut crate::leanh::LeanObject,
    mut v___y_7012_: *mut crate::leanh::LeanObject,
    mut v___y_7013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7014_: u8 = 0;
    let mut v_skipConstInApp_boxed_7015_: u8 = 0;
    let mut v_skipInstances_boxed_7016_: u8 = 0;
    let mut v_res_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7014_ = (crate::leanh::lean_unbox(v_usedLetOnly_7003_) as u8);
    v_skipConstInApp_boxed_7015_ = (crate::leanh::lean_unbox(v_skipConstInApp_7004_) as u8);
    v_skipInstances_boxed_7016_ = (crate::leanh::lean_unbox(v_skipInstances_7005_) as u8);
    v_res_7017_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0(v_fvars_7000_, v_pre_7001_, v_post_7002_, v_usedLetOnly_boxed_7014_, v_skipConstInApp_boxed_7015_, v_skipInstances_boxed_7016_, v_body_7006_, v_x_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_, v___y_7012_);
    crate::leanh::lean_dec(v___y_7012_);
    crate::leanh::lean_dec_ref(v___y_7011_);
    crate::leanh::lean_dec(v___y_7010_);
    crate::leanh::lean_dec_ref(v___y_7009_);
    crate::leanh::lean_dec(v___y_7008_);
    return v_res_7017_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(
    mut v_pre_7018_: *mut crate::leanh::LeanObject,
    mut v_post_7019_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7020_: u8,
    mut v_skipConstInApp_7021_: u8,
    mut v_skipInstances_7022_: u8,
    mut v_fvars_7023_: *mut crate::leanh::LeanObject,
    mut v_e_7024_: *mut crate::leanh::LeanObject,
    mut v_a_7025_: *mut crate::leanh::LeanObject,
    mut v___y_7026_: *mut crate::leanh::LeanObject,
    mut v___y_7027_: *mut crate::leanh::LeanObject,
    mut v___y_7028_: *mut crate::leanh::LeanObject,
    mut v___y_7029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_7024_) == 8 {
        let mut v_declName_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_7035_: u8 = 0;
        let mut v___x_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_7031_ = crate::leanh::lean_ctor_get(v_e_7024_, 0);
        crate::leanh::lean_inc(v_declName_7031_);
        v_type_7032_ = crate::leanh::lean_ctor_get(v_e_7024_, 1);
        crate::leanh::lean_inc_ref(v_type_7032_);
        v_value_7033_ = crate::leanh::lean_ctor_get(v_e_7024_, 2);
        crate::leanh::lean_inc_ref(v_value_7033_);
        v_body_7034_ = crate::leanh::lean_ctor_get(v_e_7024_, 3);
        crate::leanh::lean_inc_ref(v_body_7034_);
        v_nondep_7035_ = crate::leanh::lean_ctor_get_uint8(
            v_e_7024_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_7024_, 4);
        v___x_7036_ = lean_expr_instantiate_rev(v_type_7032_, v_fvars_7023_);
        crate::leanh::lean_dec_ref(v_type_7032_);
        crate::leanh::lean_inc_ref(v_post_7019_);
        crate::leanh::lean_inc_ref(v_pre_7018_);
        v___x_7037_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7018_, v_post_7019_, v_usedLetOnly_7020_, v_skipConstInApp_7021_, v_skipInstances_7022_, v___x_7036_, v_a_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_);
        if crate::leanh::lean_obj_tag(v___x_7037_) == 0 {
            let mut v_a_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7038_ = crate::leanh::lean_ctor_get(v___x_7037_, 0);
            crate::leanh::lean_inc(v_a_7038_);
            crate::leanh::lean_dec_ref_known(v___x_7037_, 1);
            v___x_7039_ = lean_expr_instantiate_rev(v_value_7033_, v_fvars_7023_);
            crate::leanh::lean_dec_ref(v_value_7033_);
            crate::leanh::lean_inc_ref(v_post_7019_);
            crate::leanh::lean_inc_ref(v_pre_7018_);
            v___x_7040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7018_, v_post_7019_, v_usedLetOnly_7020_, v_skipConstInApp_7021_, v_skipInstances_7022_, v___x_7039_, v_a_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_);
            if crate::leanh::lean_obj_tag(v___x_7040_) == 0 {
                let mut v_a_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7046_: u8 = 0;
                let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_7041_ = crate::leanh::lean_ctor_get(v___x_7040_, 0);
                crate::leanh::lean_inc(v_a_7041_);
                crate::leanh::lean_dec_ref_known(v___x_7040_, 1);
                v___x_7042_ = crate::leanh::lean_box((v_usedLetOnly_7020_) as usize);
                v___x_7043_ = crate::leanh::lean_box((v_skipConstInApp_7021_) as usize);
                v___x_7044_ = crate::leanh::lean_box((v_skipInstances_7022_) as usize);
                v___f_7045_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                crate::leanh::lean_closure_set(v___f_7045_, 0, v_fvars_7023_);
                crate::leanh::lean_closure_set(v___f_7045_, 1, v_pre_7018_);
                crate::leanh::lean_closure_set(v___f_7045_, 2, v_post_7019_);
                crate::leanh::lean_closure_set(v___f_7045_, 3, v___x_7042_);
                crate::leanh::lean_closure_set(v___f_7045_, 4, v___x_7043_);
                crate::leanh::lean_closure_set(v___f_7045_, 5, v___x_7044_);
                crate::leanh::lean_closure_set(v___f_7045_, 6, v_body_7034_);
                v___x_7046_ = 0;
                v___x_7047_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_declName_7031_, v_a_7038_, v_a_7041_, v___f_7045_, v_nondep_7035_, v___x_7046_, v_a_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_);
                return v___x_7047_;
            } else {
                crate::leanh::lean_dec(v_a_7038_);
                crate::leanh::lean_dec_ref(v_body_7034_);
                crate::leanh::lean_dec(v_declName_7031_);
                crate::leanh::lean_dec_ref(v_fvars_7023_);
                crate::leanh::lean_dec_ref(v_post_7019_);
                crate::leanh::lean_dec_ref(v_pre_7018_);
                return v___x_7040_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_body_7034_);
            crate::leanh::lean_dec_ref(v_value_7033_);
            crate::leanh::lean_dec(v_declName_7031_);
            crate::leanh::lean_dec_ref(v_fvars_7023_);
            crate::leanh::lean_dec_ref(v_post_7019_);
            crate::leanh::lean_dec_ref(v_pre_7018_);
            return v___x_7037_;
        }
    } else {
        let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7048_ = lean_expr_instantiate_rev(v_e_7024_, v_fvars_7023_);
        crate::leanh::lean_dec_ref(v_e_7024_);
        crate::leanh::lean_inc_ref(v_post_7019_);
        crate::leanh::lean_inc_ref(v_pre_7018_);
        v___x_7049_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7018_, v_post_7019_, v_usedLetOnly_7020_, v_skipConstInApp_7021_, v_skipInstances_7022_, v___x_7048_, v_a_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_);
        if crate::leanh::lean_obj_tag(v___x_7049_) == 0 {
            let mut v_a_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7051_: u8 = 0;
            let mut v___x_7052_: u8 = 0;
            let mut v___x_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7050_ = crate::leanh::lean_ctor_get(v___x_7049_, 0);
            crate::leanh::lean_inc(v_a_7050_);
            crate::leanh::lean_dec_ref_known(v___x_7049_, 1);
            v___x_7051_ = 0;
            v___x_7052_ = 1;
            v___x_7053_ = l_Lean_Meta_mkLetFVars(
                v_fvars_7023_,
                v_a_7050_,
                v_usedLetOnly_7020_,
                v___x_7051_,
                v___x_7052_,
                v___y_7026_,
                v___y_7027_,
                v___y_7028_,
                v___y_7029_,
            );
            crate::leanh::lean_dec_ref(v_fvars_7023_);
            if crate::leanh::lean_obj_tag(v___x_7053_) == 0 {
                let mut v_a_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_7054_ = crate::leanh::lean_ctor_get(v___x_7053_, 0);
                crate::leanh::lean_inc(v_a_7054_);
                crate::leanh::lean_dec_ref_known(v___x_7053_, 1);
                v___x_7055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7018_, v_post_7019_, v_usedLetOnly_7020_, v_skipConstInApp_7021_, v_skipInstances_7022_, v_a_7054_, v_a_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_);
                return v___x_7055_;
            } else {
                crate::leanh::lean_dec_ref(v_post_7019_);
                crate::leanh::lean_dec_ref(v_pre_7018_);
                return v___x_7053_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_7023_);
            crate::leanh::lean_dec_ref(v_post_7019_);
            crate::leanh::lean_dec_ref(v_pre_7018_);
            return v___x_7049_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(
    mut v_pre_7056_: *mut crate::leanh::LeanObject,
    mut v_post_7057_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7058_: u8,
    mut v_skipConstInApp_7059_: u8,
    mut v_skipInstances_7060_: u8,
    mut v_sz_7061_: usize,
    mut v_i_7062_: usize,
    mut v_bs_7063_: *mut crate::leanh::LeanObject,
    mut v___y_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
    mut v___y_7066_: *mut crate::leanh::LeanObject,
    mut v___y_7067_: *mut crate::leanh::LeanObject,
    mut v___y_7068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7070_: u8 = 0;
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: usize = 0;
    let mut v___x_7078_: usize = 0;
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7084_: u8 = 0;
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7070_ = lean_usize_dec_lt(v_i_7062_, v_sz_7061_);
                if v___x_7070_ == 0 {
                    crate::leanh::lean_dec_ref(v_post_7057_);
                    crate::leanh::lean_dec_ref(v_pre_7056_);
                    v___x_7071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7071_, 0, v_bs_7063_);
                    return v___x_7071_;
                } else {
                    v_v_7072_ = lean_array_uget_borrowed(v_bs_7063_, v_i_7062_);
                    crate::leanh::lean_inc(v_v_7072_);
                    crate::leanh::lean_inc_ref(v_post_7057_);
                    crate::leanh::lean_inc_ref(v_pre_7056_);
                    v___x_7073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7056_, v_post_7057_, v_usedLetOnly_7058_, v_skipConstInApp_7059_, v_skipInstances_7060_, v_v_7072_, v___y_7064_, v___y_7065_, v___y_7066_, v___y_7067_, v___y_7068_);
                    if crate::leanh::lean_obj_tag(v___x_7073_) == 0 {
                        v_a_7074_ = crate::leanh::lean_ctor_get(v___x_7073_, 0);
                        crate::leanh::lean_inc(v_a_7074_);
                        crate::leanh::lean_dec_ref_known(v___x_7073_, 1);
                        v___x_7075_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7076_ = lean_array_uset(v_bs_7063_, v_i_7062_, v___x_7075_);
                        v___x_7077_ = 1usize;
                        v___x_7078_ = lean_usize_add(v_i_7062_, v___x_7077_);
                        v___x_7079_ = lean_array_uset(v_bs_x27_7076_, v_i_7062_, v_a_7074_);
                        v_i_7062_ = v___x_7078_;
                        v_bs_7063_ = v___x_7079_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_7063_);
                        crate::leanh::lean_dec_ref(v_post_7057_);
                        crate::leanh::lean_dec_ref(v_pre_7056_);
                        v_a_7081_ = crate::leanh::lean_ctor_get(v___x_7073_, 0);
                        v_isSharedCheck_7088_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7073_)) as u8;
                        if v_isSharedCheck_7088_ == 0 {
                            v___x_7083_ = v___x_7073_;
                            v_isShared_7084_ = v_isSharedCheck_7088_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7081_);
                            crate::leanh::lean_dec(v___x_7073_);
                            v___x_7083_ = crate::leanh::lean_box(0);
                            v_isShared_7084_ = v_isSharedCheck_7088_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7084_ == 0 {
                    v___x_7086_ = v___x_7083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7087_, 0, v_a_7081_);
                    v___x_7086_ = v_reuseFailAlloc_7087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(
    mut v_pre_7089_: *mut crate::leanh::LeanObject,
    mut v_post_7090_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7091_: u8,
    mut v_skipConstInApp_7092_: u8,
    mut v_skipInstances_7093_: u8,
    mut v___x_7094_: *mut crate::leanh::LeanObject,
    mut v___y_7095_: *mut crate::leanh::LeanObject,
    mut v_b_7096_: *mut crate::leanh::LeanObject,
    mut v_a_7097_: *mut crate::leanh::LeanObject,
    mut v___y_7098_: *mut crate::leanh::LeanObject,
    mut v___y_7099_: *mut crate::leanh::LeanObject,
    mut v___y_7100_: *mut crate::leanh::LeanObject,
    mut v___y_7101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7107_: u8 = 0;
    let mut v___x_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7113_: u8 = 0;
    let mut v_a_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7117_: u8 = 0;
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7089_, v_post_7090_, v_usedLetOnly_7091_, v_skipConstInApp_7092_, v_skipInstances_7093_, v___x_7094_, v___y_7095_, v___y_7098_, v___y_7099_, v___y_7100_, v___y_7101_);
                if crate::leanh::lean_obj_tag(v___x_7103_) == 0 {
                    v_a_7104_ = crate::leanh::lean_ctor_get(v___x_7103_, 0);
                    v_isSharedCheck_7113_ = (!crate::leanh::lean_is_exclusive(v___x_7103_)) as u8;
                    if v_isSharedCheck_7113_ == 0 {
                        v___x_7106_ = v___x_7103_;
                        v_isShared_7107_ = v_isSharedCheck_7113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7104_);
                        crate::leanh::lean_dec(v___x_7103_);
                        v___x_7106_ = crate::leanh::lean_box(0);
                        v_isShared_7107_ = v_isSharedCheck_7113_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_7096_);
                    v_a_7114_ = crate::leanh::lean_ctor_get(v___x_7103_, 0);
                    v_isSharedCheck_7121_ = (!crate::leanh::lean_is_exclusive(v___x_7103_)) as u8;
                    if v_isSharedCheck_7121_ == 0 {
                        v___x_7116_ = v___x_7103_;
                        v_isShared_7117_ = v_isSharedCheck_7121_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7114_);
                        crate::leanh::lean_dec(v___x_7103_);
                        v___x_7116_ = crate::leanh::lean_box(0);
                        v_isShared_7117_ = v_isSharedCheck_7121_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7108_ = lean_array_fset(v_b_7096_, v_a_7097_, v_a_7104_);
                v___x_7109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7109_, 0, v___x_7108_);
                if v_isShared_7107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7106_, 0, v___x_7109_);
                    v___x_7111_ = v___x_7106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7112_, 0, v___x_7109_);
                    v___x_7111_ = v_reuseFailAlloc_7112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7111_;
            }
            3 => {
                if v_isShared_7117_ == 0 {
                    v___x_7119_ = v___x_7116_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7120_, 0, v_a_7114_);
                    v___x_7119_ = v_reuseFailAlloc_7120_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed(
    mut v_pre_7122_: *mut crate::leanh::LeanObject,
    mut v_post_7123_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7124_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7125_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7126_: *mut crate::leanh::LeanObject,
    mut v___x_7127_: *mut crate::leanh::LeanObject,
    mut v___y_7128_: *mut crate::leanh::LeanObject,
    mut v_b_7129_: *mut crate::leanh::LeanObject,
    mut v_a_7130_: *mut crate::leanh::LeanObject,
    mut v___y_7131_: *mut crate::leanh::LeanObject,
    mut v___y_7132_: *mut crate::leanh::LeanObject,
    mut v___y_7133_: *mut crate::leanh::LeanObject,
    mut v___y_7134_: *mut crate::leanh::LeanObject,
    mut v___y_7135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7136_: u8 = 0;
    let mut v_skipConstInApp_boxed_7137_: u8 = 0;
    let mut v_skipInstances_boxed_7138_: u8 = 0;
    let mut v_res_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7136_ = (crate::leanh::lean_unbox(v_usedLetOnly_7124_) as u8);
    v_skipConstInApp_boxed_7137_ = (crate::leanh::lean_unbox(v_skipConstInApp_7125_) as u8);
    v_skipInstances_boxed_7138_ = (crate::leanh::lean_unbox(v_skipInstances_7126_) as u8);
    v_res_7139_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0(v_pre_7122_, v_post_7123_, v_usedLetOnly_boxed_7136_, v_skipConstInApp_boxed_7137_, v_skipInstances_boxed_7138_, v___x_7127_, v___y_7128_, v_b_7129_, v_a_7130_, v___y_7131_, v___y_7132_, v___y_7133_, v___y_7134_);
    crate::leanh::lean_dec(v___y_7134_);
    crate::leanh::lean_dec_ref(v___y_7133_);
    crate::leanh::lean_dec(v___y_7132_);
    crate::leanh::lean_dec_ref(v___y_7131_);
    crate::leanh::lean_dec(v_a_7130_);
    crate::leanh::lean_dec(v___y_7128_);
    return v_res_7139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(
    mut v_upperBound_7140_: *mut crate::leanh::LeanObject,
    mut v___x_7141_: *mut crate::leanh::LeanObject,
    mut v_pre_7142_: *mut crate::leanh::LeanObject,
    mut v_post_7143_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7144_: u8,
    mut v_skipConstInApp_7145_: u8,
    mut v_skipInstances_7146_: u8,
    mut v_a_7147_: *mut crate::leanh::LeanObject,
    mut v_b_7148_: *mut crate::leanh::LeanObject,
    mut v___y_7149_: *mut crate::leanh::LeanObject,
    mut v___y_7150_: *mut crate::leanh::LeanObject,
    mut v___y_7151_: *mut crate::leanh::LeanObject,
    mut v___y_7152_: *mut crate::leanh::LeanObject,
    mut v___y_7153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7161_: u8 = 0;
    let mut v_a_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7170_: u8 = 0;
    let mut v_a_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7174_: u8 = 0;
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7178_: u8 = 0;
    let mut v___x_7179_: u8 = 0;
    let mut v___x_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: u8 = 0;
    let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_7189_: u8 = 0;
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7179_ = lean_nat_dec_lt(v_a_7147_, v_upperBound_7140_);
                if v___x_7179_ == 0 {
                    crate::leanh::lean_dec(v_a_7147_);
                    crate::leanh::lean_dec_ref(v_post_7143_);
                    crate::leanh::lean_dec_ref(v_pre_7142_);
                    v___x_7180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7180_, 0, v_b_7148_);
                    return v___x_7180_;
                } else {
                    v___x_7181_ = lean_array_fget_borrowed(v_b_7148_, v_a_7147_);
                    v___x_7182_ = lean_array_get_size(v___x_7141_);
                    v___x_7183_ = lean_nat_dec_lt(v_a_7147_, v___x_7182_);
                    if v___x_7183_ == 0 {
                        crate::leanh::lean_inc(v___x_7181_);
                        v___x_7184_ = crate::leanh::lean_box((v_usedLetOnly_7144_) as usize);
                        v___x_7185_ = crate::leanh::lean_box((v_skipConstInApp_7145_) as usize);
                        v___x_7186_ = crate::leanh::lean_box((v_skipInstances_7146_) as usize);
                        crate::leanh::lean_inc(v_a_7147_);
                        crate::leanh::lean_inc(v___y_7149_);
                        crate::leanh::lean_inc_ref(v_post_7143_);
                        crate::leanh::lean_inc_ref(v_pre_7142_);
                        v___f_7187_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                        crate::leanh::lean_closure_set(v___f_7187_, 0, v_pre_7142_);
                        crate::leanh::lean_closure_set(v___f_7187_, 1, v_post_7143_);
                        crate::leanh::lean_closure_set(v___f_7187_, 2, v___x_7184_);
                        crate::leanh::lean_closure_set(v___f_7187_, 3, v___x_7185_);
                        crate::leanh::lean_closure_set(v___f_7187_, 4, v___x_7186_);
                        crate::leanh::lean_closure_set(v___f_7187_, 5, v___x_7181_);
                        crate::leanh::lean_closure_set(v___f_7187_, 6, v___y_7149_);
                        crate::leanh::lean_closure_set(v___f_7187_, 7, v_b_7148_);
                        crate::leanh::lean_closure_set(v___f_7187_, 8, v_a_7147_);
                        v___y_7156_ = v___f_7187_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7188_ = lean_array_fget_borrowed(v___x_7141_, v_a_7147_);
                        v_isInstance_7189_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_7188_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 4) as u32,
                        );
                        if v_isInstance_7189_ == 0 {
                            crate::leanh::lean_inc(v___x_7181_);
                            v___x_7190_ = crate::leanh::lean_box((v_usedLetOnly_7144_) as usize);
                            v___x_7191_ = crate::leanh::lean_box((v_skipConstInApp_7145_) as usize);
                            v___x_7192_ = crate::leanh::lean_box((v_skipInstances_7146_) as usize);
                            crate::leanh::lean_inc(v_a_7147_);
                            crate::leanh::lean_inc(v___y_7149_);
                            crate::leanh::lean_inc_ref(v_post_7143_);
                            crate::leanh::lean_inc_ref(v_pre_7142_);
                            v___f_7193_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 9);
                            crate::leanh::lean_closure_set(v___f_7193_, 0, v_pre_7142_);
                            crate::leanh::lean_closure_set(v___f_7193_, 1, v_post_7143_);
                            crate::leanh::lean_closure_set(v___f_7193_, 2, v___x_7190_);
                            crate::leanh::lean_closure_set(v___f_7193_, 3, v___x_7191_);
                            crate::leanh::lean_closure_set(v___f_7193_, 4, v___x_7192_);
                            crate::leanh::lean_closure_set(v___f_7193_, 5, v___x_7181_);
                            crate::leanh::lean_closure_set(v___f_7193_, 6, v___y_7149_);
                            crate::leanh::lean_closure_set(v___f_7193_, 7, v_b_7148_);
                            crate::leanh::lean_closure_set(v___f_7193_, 8, v_a_7147_);
                            v___y_7156_ = v___f_7193_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7194_, 0, v_b_7148_);
                            v___f_7195_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 1);
                            crate::leanh::lean_closure_set(v___f_7195_, 0, v___x_7194_);
                            v___y_7156_ = v___f_7195_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_7153_);
                crate::leanh::lean_inc_ref(v___y_7152_);
                crate::leanh::lean_inc(v___y_7151_);
                crate::leanh::lean_inc_ref(v___y_7150_);
                v___x_7157_ = crate::leanh::lean_apply_5(
                    v___y_7156_,
                    v___y_7150_,
                    v___y_7151_,
                    v___y_7152_,
                    v___y_7153_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_7157_) == 0 {
                    v_a_7158_ = crate::leanh::lean_ctor_get(v___x_7157_, 0);
                    v_isSharedCheck_7170_ = (!crate::leanh::lean_is_exclusive(v___x_7157_)) as u8;
                    if v_isSharedCheck_7170_ == 0 {
                        v___x_7160_ = v___x_7157_;
                        v_isShared_7161_ = v_isSharedCheck_7170_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7158_);
                        crate::leanh::lean_dec(v___x_7157_);
                        v___x_7160_ = crate::leanh::lean_box(0);
                        v_isShared_7161_ = v_isSharedCheck_7170_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7147_);
                    crate::leanh::lean_dec_ref(v_post_7143_);
                    crate::leanh::lean_dec_ref(v_pre_7142_);
                    v_a_7171_ = crate::leanh::lean_ctor_get(v___x_7157_, 0);
                    v_isSharedCheck_7178_ = (!crate::leanh::lean_is_exclusive(v___x_7157_)) as u8;
                    if v_isSharedCheck_7178_ == 0 {
                        v___x_7173_ = v___x_7157_;
                        v_isShared_7174_ = v_isSharedCheck_7178_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7171_);
                        crate::leanh::lean_dec(v___x_7157_);
                        v___x_7173_ = crate::leanh::lean_box(0);
                        v_isShared_7174_ = v_isSharedCheck_7178_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7158_) == 0 {
                    crate::leanh::lean_dec(v_a_7147_);
                    crate::leanh::lean_dec_ref(v_post_7143_);
                    crate::leanh::lean_dec_ref(v_pre_7142_);
                    v_a_7162_ = crate::leanh::lean_ctor_get(v_a_7158_, 0);
                    crate::leanh::lean_inc(v_a_7162_);
                    crate::leanh::lean_dec_ref_known(v_a_7158_, 1);
                    if v_isShared_7161_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7160_, 0, v_a_7162_);
                        v___x_7164_ = v___x_7160_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 0, v_a_7162_);
                        v___x_7164_ = v_reuseFailAlloc_7165_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7160_);
                    v_a_7166_ = crate::leanh::lean_ctor_get(v_a_7158_, 0);
                    crate::leanh::lean_inc(v_a_7166_);
                    crate::leanh::lean_dec_ref_known(v_a_7158_, 1);
                    v___x_7167_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7168_ = lean_nat_add(v_a_7147_, v___x_7167_);
                    crate::leanh::lean_dec(v_a_7147_);
                    v_a_7147_ = v___x_7168_;
                    v_b_7148_ = v_a_7166_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_7164_;
            }
            4 => {
                if v_isShared_7174_ == 0 {
                    v___x_7176_ = v___x_7173_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7177_, 0, v_a_7171_);
                    v___x_7176_ = v_reuseFailAlloc_7177_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(
    mut v_skipInstances_7196_: u8,
    mut v_pre_7197_: *mut crate::leanh::LeanObject,
    mut v_post_7198_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7199_: u8,
    mut v_skipConstInApp_7200_: u8,
    mut v_x_7201_: *mut crate::leanh::LeanObject,
    mut v_x_7202_: *mut crate::leanh::LeanObject,
    mut v_x_7203_: *mut crate::leanh::LeanObject,
    mut v___y_7204_: *mut crate::leanh::LeanObject,
    mut v___y_7205_: *mut crate::leanh::LeanObject,
    mut v___y_7206_: *mut crate::leanh::LeanObject,
    mut v___y_7207_: *mut crate::leanh::LeanObject,
    mut v___y_7208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7217_: usize = 0;
    let mut v___x_7218_: usize = 0;
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7226_: u8 = 0;
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7230_: u8 = 0;
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7243_: u8 = 0;
    let mut v___x_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7247_: u8 = 0;
    let mut v_a_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7251_: u8 = 0;
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7255_: u8 = 0;
    let mut v___x_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7201_) == 5 {
                    v_fn_7259_ = crate::leanh::lean_ctor_get(v_x_7201_, 0);
                    crate::leanh::lean_inc_ref(v_fn_7259_);
                    v_arg_7260_ = crate::leanh::lean_ctor_get(v_x_7201_, 1);
                    crate::leanh::lean_inc_ref(v_arg_7260_);
                    crate::leanh::lean_dec_ref_known(v_x_7201_, 2);
                    v___x_7261_ = lean_array_set(v_x_7202_, v_x_7203_, v_arg_7260_);
                    v___x_7262_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7263_ = lean_nat_sub(v_x_7203_, v___x_7262_);
                    crate::leanh::lean_dec(v_x_7203_);
                    v_x_7201_ = v_fn_7259_;
                    v_x_7202_ = v___x_7261_;
                    v_x_7203_ = v___x_7263_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_7203_);
                    if v_skipConstInApp_7200_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_7265_ = l_Lean_Expr_isConst(v_x_7201_);
                        if v___x_7265_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v_f_7211_ = v_x_7201_;
                            v___y_7212_ = v___y_7204_;
                            v___y_7213_ = v___y_7205_;
                            v___y_7214_ = v___y_7206_;
                            v___y_7215_ = v___y_7207_;
                            v___y_7216_ = v___y_7208_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_skipInstances_7196_ == 0 {
                    v_sz_7217_ = lean_array_size(v_x_7202_);
                    v___x_7218_ = 0usize;
                    crate::leanh::lean_inc_ref(v_post_7198_);
                    crate::leanh::lean_inc_ref(v_pre_7197_);
                    v___x_7219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_7197_, v_post_7198_, v_usedLetOnly_7199_, v_skipConstInApp_7200_, v_skipInstances_7196_, v_sz_7217_, v___x_7218_, v_x_7202_, v___y_7212_, v___y_7213_, v___y_7214_, v___y_7215_, v___y_7216_);
                    if crate::leanh::lean_obj_tag(v___x_7219_) == 0 {
                        v_a_7220_ = crate::leanh::lean_ctor_get(v___x_7219_, 0);
                        crate::leanh::lean_inc(v_a_7220_);
                        crate::leanh::lean_dec_ref_known(v___x_7219_, 1);
                        v___x_7221_ = l_Lean_mkAppN(v_f_7211_, v_a_7220_);
                        crate::leanh::lean_dec(v_a_7220_);
                        v___x_7222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7197_, v_post_7198_, v_usedLetOnly_7199_, v_skipConstInApp_7200_, v_skipInstances_7196_, v___x_7221_, v___y_7212_, v___y_7213_, v___y_7214_, v___y_7215_, v___y_7216_);
                        return v___x_7222_;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_7211_);
                        crate::leanh::lean_dec_ref(v_post_7198_);
                        crate::leanh::lean_dec_ref(v_pre_7197_);
                        v_a_7223_ = crate::leanh::lean_ctor_get(v___x_7219_, 0);
                        v_isSharedCheck_7230_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7219_)) as u8;
                        if v_isSharedCheck_7230_ == 0 {
                            v___x_7225_ = v___x_7219_;
                            v_isShared_7226_ = v_isSharedCheck_7230_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7223_);
                            crate::leanh::lean_dec(v___x_7219_);
                            v___x_7225_ = crate::leanh::lean_box(0);
                            v_isShared_7226_ = v_isSharedCheck_7230_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_7231_ = lean_array_get_size(v_x_7202_);
                    crate::leanh::lean_inc_ref(v_f_7211_);
                    v___x_7232_ = l_Lean_Meta_getFunInfoNArgs(
                        v_f_7211_,
                        v___x_7231_,
                        v___y_7213_,
                        v___y_7214_,
                        v___y_7215_,
                        v___y_7216_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7232_) == 0 {
                        v_a_7233_ = crate::leanh::lean_ctor_get(v___x_7232_, 0);
                        crate::leanh::lean_inc(v_a_7233_);
                        crate::leanh::lean_dec_ref_known(v___x_7232_, 1);
                        v_paramInfo_7234_ = crate::leanh::lean_ctor_get(v_a_7233_, 0);
                        crate::leanh::lean_inc_ref(v_paramInfo_7234_);
                        crate::leanh::lean_dec(v_a_7233_);
                        v___x_7235_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_post_7198_);
                        crate::leanh::lean_inc_ref(v_pre_7197_);
                        v___x_7236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v___x_7231_, v_paramInfo_7234_, v_pre_7197_, v_post_7198_, v_usedLetOnly_7199_, v_skipConstInApp_7200_, v_skipInstances_7196_, v___x_7235_, v_x_7202_, v___y_7212_, v___y_7213_, v___y_7214_, v___y_7215_, v___y_7216_);
                        crate::leanh::lean_dec_ref(v_paramInfo_7234_);
                        if crate::leanh::lean_obj_tag(v___x_7236_) == 0 {
                            v_a_7237_ = crate::leanh::lean_ctor_get(v___x_7236_, 0);
                            crate::leanh::lean_inc(v_a_7237_);
                            crate::leanh::lean_dec_ref_known(v___x_7236_, 1);
                            v___x_7238_ = l_Lean_mkAppN(v_f_7211_, v_a_7237_);
                            crate::leanh::lean_dec(v_a_7237_);
                            v___x_7239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7197_, v_post_7198_, v_usedLetOnly_7199_, v_skipConstInApp_7200_, v_skipInstances_7196_, v___x_7238_, v___y_7212_, v___y_7213_, v___y_7214_, v___y_7215_, v___y_7216_);
                            return v___x_7239_;
                        } else {
                            crate::leanh::lean_dec_ref(v_f_7211_);
                            crate::leanh::lean_dec_ref(v_post_7198_);
                            crate::leanh::lean_dec_ref(v_pre_7197_);
                            v_a_7240_ = crate::leanh::lean_ctor_get(v___x_7236_, 0);
                            v_isSharedCheck_7247_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7236_)) as u8;
                            if v_isSharedCheck_7247_ == 0 {
                                v___x_7242_ = v___x_7236_;
                                v_isShared_7243_ = v_isSharedCheck_7247_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7240_);
                                crate::leanh::lean_dec(v___x_7236_);
                                v___x_7242_ = crate::leanh::lean_box(0);
                                v_isShared_7243_ = v_isSharedCheck_7247_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_7211_);
                        crate::leanh::lean_dec_ref(v_x_7202_);
                        crate::leanh::lean_dec_ref(v_post_7198_);
                        crate::leanh::lean_dec_ref(v_pre_7197_);
                        v_a_7248_ = crate::leanh::lean_ctor_get(v___x_7232_, 0);
                        v_isSharedCheck_7255_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7232_)) as u8;
                        if v_isSharedCheck_7255_ == 0 {
                            v___x_7250_ = v___x_7232_;
                            v_isShared_7251_ = v_isSharedCheck_7255_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7248_);
                            crate::leanh::lean_dec(v___x_7232_);
                            v___x_7250_ = crate::leanh::lean_box(0);
                            v_isShared_7251_ = v_isSharedCheck_7255_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_7226_ == 0 {
                    v___x_7228_ = v___x_7225_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 0, v_a_7223_);
                    v___x_7228_ = v_reuseFailAlloc_7229_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7228_;
            }
            4 => {
                if v_isShared_7243_ == 0 {
                    v___x_7245_ = v___x_7242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7246_, 0, v_a_7240_);
                    v___x_7245_ = v_reuseFailAlloc_7246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7245_;
            }
            6 => {
                if v_isShared_7251_ == 0 {
                    v___x_7253_ = v___x_7250_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7254_, 0, v_a_7248_);
                    v___x_7253_ = v_reuseFailAlloc_7254_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7253_;
            }
            8 => {
                crate::leanh::lean_inc_ref(v_post_7198_);
                crate::leanh::lean_inc_ref(v_pre_7197_);
                v___x_7257_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7197_, v_post_7198_, v_usedLetOnly_7199_, v_skipConstInApp_7200_, v_skipInstances_7196_, v_x_7201_, v___y_7204_, v___y_7205_, v___y_7206_, v___y_7207_, v___y_7208_);
                if crate::leanh::lean_obj_tag(v___x_7257_) == 0 {
                    v_a_7258_ = crate::leanh::lean_ctor_get(v___x_7257_, 0);
                    crate::leanh::lean_inc(v_a_7258_);
                    crate::leanh::lean_dec_ref_known(v___x_7257_, 1);
                    v_f_7211_ = v_a_7258_;
                    v___y_7212_ = v___y_7204_;
                    v___y_7213_ = v___y_7205_;
                    v___y_7214_ = v___y_7206_;
                    v___y_7215_ = v___y_7207_;
                    v___y_7216_ = v___y_7208_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_x_7202_);
                    crate::leanh::lean_dec_ref(v_post_7198_);
                    crate::leanh::lean_dec_ref(v_pre_7197_);
                    return v___x_7257_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(
    mut v___x_7266_: *mut crate::leanh::LeanObject,
    mut v_pre_7267_: *mut crate::leanh::LeanObject,
    mut v_e_7268_: *mut crate::leanh::LeanObject,
    mut v_post_7269_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7270_: u8,
    mut v_skipConstInApp_7271_: u8,
    mut v_skipInstances_7272_: u8,
    mut v___y_7273_: *mut crate::leanh::LeanObject,
    mut v___y_7274_: *mut crate::leanh::LeanObject,
    mut v___y_7275_: *mut crate::leanh::LeanObject,
    mut v___y_7276_: *mut crate::leanh::LeanObject,
    mut v___y_7277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7284_: u8 = 0;
    let mut v___y_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: usize = 0;
    let mut v___x_7304_: usize = 0;
    let mut v___x_7305_: u8 = 0;
    let mut v___x_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: usize = 0;
    let mut v___x_7315_: usize = 0;
    let mut v___x_7316_: u8 = 0;
    let mut v___x_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x3f_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7329_: u8 = 0;
    let mut v_a_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7333_: u8 = 0;
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7337_: u8 = 0;
    let mut v_a_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7341_: u8 = 0;
    let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7279_ = l_Lean_Core_checkSystem(v___x_7266_, v___y_7276_, v___y_7277_);
                if crate::leanh::lean_obj_tag(v___x_7279_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7279_, 1);
                    crate::leanh::lean_inc_ref(v_pre_7267_);
                    crate::leanh::lean_inc(v___y_7277_);
                    crate::leanh::lean_inc_ref(v___y_7276_);
                    crate::leanh::lean_inc(v___y_7275_);
                    crate::leanh::lean_inc_ref(v___y_7274_);
                    crate::leanh::lean_inc_ref(v_e_7268_);
                    v___x_7280_ = crate::leanh::lean_apply_6(
                        v_pre_7267_,
                        v_e_7268_,
                        v___y_7274_,
                        v___y_7275_,
                        v___y_7276_,
                        v___y_7277_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7280_) == 0 {
                        v_a_7281_ = crate::leanh::lean_ctor_get(v___x_7280_, 0);
                        v_isSharedCheck_7329_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7280_)) as u8;
                        if v_isSharedCheck_7329_ == 0 {
                            v___x_7283_ = v___x_7280_;
                            v_isShared_7284_ = v_isSharedCheck_7329_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7281_);
                            crate::leanh::lean_dec(v___x_7280_);
                            v___x_7283_ = crate::leanh::lean_box(0);
                            v_isShared_7284_ = v_isSharedCheck_7329_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_post_7269_);
                        crate::leanh::lean_dec_ref(v_e_7268_);
                        crate::leanh::lean_dec_ref(v_pre_7267_);
                        v_a_7330_ = crate::leanh::lean_ctor_get(v___x_7280_, 0);
                        v_isSharedCheck_7337_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7280_)) as u8;
                        if v_isSharedCheck_7337_ == 0 {
                            v___x_7332_ = v___x_7280_;
                            v_isShared_7333_ = v_isSharedCheck_7337_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7330_);
                            crate::leanh::lean_dec(v___x_7280_);
                            v___x_7332_ = crate::leanh::lean_box(0);
                            v_isShared_7333_ = v_isSharedCheck_7337_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_post_7269_);
                    crate::leanh::lean_dec_ref(v_e_7268_);
                    crate::leanh::lean_dec_ref(v_pre_7267_);
                    v_a_7338_ = crate::leanh::lean_ctor_get(v___x_7279_, 0);
                    v_isSharedCheck_7345_ = (!crate::leanh::lean_is_exclusive(v___x_7279_)) as u8;
                    if v_isSharedCheck_7345_ == 0 {
                        v___x_7340_ = v___x_7279_;
                        v_isShared_7341_ = v_isSharedCheck_7345_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7338_);
                        crate::leanh::lean_dec(v___x_7279_);
                        v___x_7340_ = crate::leanh::lean_box(0);
                        v_isShared_7341_ = v_isSharedCheck_7345_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_a_7281_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_post_7269_);
                    crate::leanh::lean_dec_ref(v_e_7268_);
                    crate::leanh::lean_dec_ref(v_pre_7267_);
                    v_e_7321_ = crate::leanh::lean_ctor_get(v_a_7281_, 0);
                    crate::leanh::lean_inc_ref(v_e_7321_);
                    crate::leanh::lean_dec_ref_known(v_a_7281_, 1);
                    if v_isShared_7284_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7283_, 0, v_e_7321_);
                        v___x_7323_ = v___x_7283_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7324_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 0, v_e_7321_);
                        v___x_7323_ = v_reuseFailAlloc_7324_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_del_object(v___x_7283_);
                    crate::leanh::lean_dec_ref(v_e_7268_);
                    v_e_7325_ = crate::leanh::lean_ctor_get(v_a_7281_, 0);
                    crate::leanh::lean_inc_ref(v_e_7325_);
                    crate::leanh::lean_dec_ref_known(v_a_7281_, 1);
                    v___x_7326_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v_e_7325_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    return v___x_7326_;
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_7283_);
                    v_e_x3f_7327_ = crate::leanh::lean_ctor_get(v_a_7281_, 0);
                    crate::leanh::lean_inc(v_e_x3f_7327_);
                    crate::leanh::lean_dec_ref_known(v_a_7281_, 1);
                    if crate::leanh::lean_obj_tag(v_e_x3f_7327_) == 0 {
                        v___y_7286_ = v_e_7268_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7268_);
                        v_val_7328_ = crate::leanh::lean_ctor_get(v_e_x3f_7327_, 0);
                        crate::leanh::lean_inc(v_val_7328_);
                        crate::leanh::lean_dec_ref_known(v_e_x3f_7327_, 1);
                        v___y_7286_ = v_val_7328_;
                        state = 2;
                        continue;
                    }
                }
            },
            2 => match crate::leanh::lean_obj_tag(v___y_7286_) {
                7 => {
                    v___x_7287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0;
                    v___x_7288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___x_7287_, v___y_7286_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    return v___x_7288_;
                }
                6 => {
                    v___x_7289_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0;
                    v___x_7290_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___x_7289_, v___y_7286_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    return v___x_7290_;
                }
                8 => {
                    v___x_7291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___closed__0;
                    v___x_7292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___x_7291_, v___y_7286_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    return v___x_7292_;
                }
                5 => {
                    v_dummy_7293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0_once), _init_l___private_Lean_Meta_Structure_0__Lean_Meta_etaStruct_x3f_getProjectedExpr___closed__0);
                    v_nargs_7294_ = l_Lean_Expr_getAppNumArgs(v___y_7286_);
                    crate::leanh::lean_inc(v_nargs_7294_);
                    v___x_7295_ = lean_mk_array(v_nargs_7294_, v_dummy_7293_);
                    v___x_7296_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7297_ = lean_nat_sub(v_nargs_7294_, v___x_7296_);
                    crate::leanh::lean_dec(v_nargs_7294_);
                    v___x_7298_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_7272_, v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v___y_7286_, v___x_7295_, v___x_7297_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    return v___x_7298_;
                }
                10 => {
                    v_data_7299_ = crate::leanh::lean_ctor_get(v___y_7286_, 0);
                    v_expr_7300_ = crate::leanh::lean_ctor_get(v___y_7286_, 1);
                    crate::leanh::lean_inc_ref(v_expr_7300_);
                    crate::leanh::lean_inc_ref(v_post_7269_);
                    crate::leanh::lean_inc_ref(v_pre_7267_);
                    v___x_7301_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v_expr_7300_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    if crate::leanh::lean_obj_tag(v___x_7301_) == 0 {
                        v_a_7302_ = crate::leanh::lean_ctor_get(v___x_7301_, 0);
                        crate::leanh::lean_inc(v_a_7302_);
                        crate::leanh::lean_dec_ref_known(v___x_7301_, 1);
                        v___x_7303_ = lean_ptr_addr(v_expr_7300_);
                        v___x_7304_ = lean_ptr_addr(v_a_7302_);
                        v___x_7305_ = lean_usize_dec_eq(v___x_7303_, v___x_7304_);
                        if v___x_7305_ == 0 {
                            crate::leanh::lean_inc(v_data_7299_);
                            crate::leanh::lean_dec_ref_known(v___y_7286_, 2);
                            v___x_7306_ = l_Lean_Expr_mdata___override(v_data_7299_, v_a_7302_);
                            v___x_7307_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___x_7306_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                            return v___x_7307_;
                        } else {
                            crate::leanh::lean_dec(v_a_7302_);
                            v___x_7308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___y_7286_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                            return v___x_7308_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_7286_, 2);
                        crate::leanh::lean_dec_ref(v_post_7269_);
                        crate::leanh::lean_dec_ref(v_pre_7267_);
                        return v___x_7301_;
                    }
                }
                11 => {
                    v_typeName_7309_ = crate::leanh::lean_ctor_get(v___y_7286_, 0);
                    v_idx_7310_ = crate::leanh::lean_ctor_get(v___y_7286_, 1);
                    v_struct_7311_ = crate::leanh::lean_ctor_get(v___y_7286_, 2);
                    crate::leanh::lean_inc_ref(v_struct_7311_);
                    crate::leanh::lean_inc_ref(v_post_7269_);
                    crate::leanh::lean_inc_ref(v_pre_7267_);
                    v___x_7312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v_struct_7311_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    if crate::leanh::lean_obj_tag(v___x_7312_) == 0 {
                        v_a_7313_ = crate::leanh::lean_ctor_get(v___x_7312_, 0);
                        crate::leanh::lean_inc(v_a_7313_);
                        crate::leanh::lean_dec_ref_known(v___x_7312_, 1);
                        v___x_7314_ = lean_ptr_addr(v_struct_7311_);
                        v___x_7315_ = lean_ptr_addr(v_a_7313_);
                        v___x_7316_ = lean_usize_dec_eq(v___x_7314_, v___x_7315_);
                        if v___x_7316_ == 0 {
                            crate::leanh::lean_inc(v_idx_7310_);
                            crate::leanh::lean_inc(v_typeName_7309_);
                            crate::leanh::lean_dec_ref_known(v___y_7286_, 3);
                            v___x_7317_ = l_Lean_Expr_proj___override(
                                v_typeName_7309_,
                                v_idx_7310_,
                                v_a_7313_,
                            );
                            v___x_7318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___x_7317_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                            return v___x_7318_;
                        } else {
                            crate::leanh::lean_dec(v_a_7313_);
                            v___x_7319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___y_7286_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                            return v___x_7319_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_7286_, 3);
                        crate::leanh::lean_dec_ref(v_post_7269_);
                        crate::leanh::lean_dec_ref(v_pre_7267_);
                        return v___x_7312_;
                    }
                }
                _ => {
                    v___x_7320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7267_, v_post_7269_, v_usedLetOnly_7270_, v_skipConstInApp_7271_, v_skipInstances_7272_, v___y_7286_, v___y_7273_, v___y_7274_, v___y_7275_, v___y_7276_, v___y_7277_);
                    return v___x_7320_;
                }
            },
            3 => {
                return v___x_7323_;
            }
            4 => {
                if v_isShared_7333_ == 0 {
                    v___x_7335_ = v___x_7332_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7336_, 0, v_a_7330_);
                    v___x_7335_ = v_reuseFailAlloc_7336_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7335_;
            }
            6 => {
                if v_isShared_7341_ == 0 {
                    v___x_7343_ = v___x_7340_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7344_, 0, v_a_7338_);
                    v___x_7343_ = v_reuseFailAlloc_7344_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed(
    mut v___x_7346_: *mut crate::leanh::LeanObject,
    mut v_pre_7347_: *mut crate::leanh::LeanObject,
    mut v_e_7348_: *mut crate::leanh::LeanObject,
    mut v_post_7349_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7350_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7351_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7352_: *mut crate::leanh::LeanObject,
    mut v___y_7353_: *mut crate::leanh::LeanObject,
    mut v___y_7354_: *mut crate::leanh::LeanObject,
    mut v___y_7355_: *mut crate::leanh::LeanObject,
    mut v___y_7356_: *mut crate::leanh::LeanObject,
    mut v___y_7357_: *mut crate::leanh::LeanObject,
    mut v___y_7358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7359_: u8 = 0;
    let mut v_skipConstInApp_boxed_7360_: u8 = 0;
    let mut v_skipInstances_boxed_7361_: u8 = 0;
    let mut v_res_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7359_ = (crate::leanh::lean_unbox(v_usedLetOnly_7350_) as u8);
    v_skipConstInApp_boxed_7360_ = (crate::leanh::lean_unbox(v_skipConstInApp_7351_) as u8);
    v_skipInstances_boxed_7361_ = (crate::leanh::lean_unbox(v_skipInstances_7352_) as u8);
    v_res_7362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1(v___x_7346_, v_pre_7347_, v_e_7348_, v_post_7349_, v_usedLetOnly_boxed_7359_, v_skipConstInApp_boxed_7360_, v_skipInstances_boxed_7361_, v___y_7353_, v___y_7354_, v___y_7355_, v___y_7356_, v___y_7357_);
    crate::leanh::lean_dec(v___y_7357_);
    crate::leanh::lean_dec_ref(v___y_7356_);
    crate::leanh::lean_dec(v___y_7355_);
    crate::leanh::lean_dec_ref(v___y_7354_);
    crate::leanh::lean_dec(v___y_7353_);
    return v_res_7362_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(
    mut v_pre_7363_: *mut crate::leanh::LeanObject,
    mut v_post_7364_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7365_: u8,
    mut v_skipConstInApp_7366_: u8,
    mut v_skipInstances_7367_: u8,
    mut v_e_7368_: *mut crate::leanh::LeanObject,
    mut v_a_7369_: *mut crate::leanh::LeanObject,
    mut v___y_7370_: *mut crate::leanh::LeanObject,
    mut v___y_7371_: *mut crate::leanh::LeanObject,
    mut v___y_7372_: *mut crate::leanh::LeanObject,
    mut v___y_7373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7380_: u8 = 0;
    let mut v___x_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7393_: u8 = 0;
    let mut v___x_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7397_: u8 = 0;
    let mut v_unused_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7402_: u8 = 0;
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7406_: u8 = 0;
    let mut v_val_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7411_: u8 = 0;
    let mut v_a_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7415_: u8 = 0;
    let mut v___x_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_7369_);
                v___x_7375_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_7375_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_7375_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_7375_, 2, v_a_7369_);
                v___x_7376_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(crate::leanh::lean_box(0), v___x_7375_, v___y_7370_, v___y_7371_, v___y_7372_, v___y_7373_);
                if crate::leanh::lean_obj_tag(v___x_7376_) == 0 {
                    v_a_7377_ = crate::leanh::lean_ctor_get(v___x_7376_, 0);
                    v_isSharedCheck_7411_ = (!crate::leanh::lean_is_exclusive(v___x_7376_)) as u8;
                    if v_isSharedCheck_7411_ == 0 {
                        v___x_7379_ = v___x_7376_;
                        v_isShared_7380_ = v_isSharedCheck_7411_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7377_);
                        crate::leanh::lean_dec(v___x_7376_);
                        v___x_7379_ = crate::leanh::lean_box(0);
                        v_isShared_7380_ = v_isSharedCheck_7411_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7368_);
                    crate::leanh::lean_dec_ref(v_post_7364_);
                    crate::leanh::lean_dec_ref(v_pre_7363_);
                    v_a_7412_ = crate::leanh::lean_ctor_get(v___x_7376_, 0);
                    v_isSharedCheck_7419_ = (!crate::leanh::lean_is_exclusive(v___x_7376_)) as u8;
                    if v_isSharedCheck_7419_ == 0 {
                        v___x_7414_ = v___x_7376_;
                        v_isShared_7415_ = v_isSharedCheck_7419_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7412_);
                        crate::leanh::lean_dec(v___x_7376_);
                        v___x_7414_ = crate::leanh::lean_box(0);
                        v_isShared_7415_ = v_isSharedCheck_7419_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7381_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_a_7377_, v_e_7368_);
                crate::leanh::lean_dec(v_a_7377_);
                if crate::leanh::lean_obj_tag(v___x_7381_) == 0 {
                    crate::leanh::lean_del_object(v___x_7379_);
                    v___x_7382_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___closed__0;
                    v___x_7383_ = crate::leanh::lean_box((v_usedLetOnly_7365_) as usize);
                    v___x_7384_ = crate::leanh::lean_box((v_skipConstInApp_7366_) as usize);
                    v___x_7385_ = crate::leanh::lean_box((v_skipInstances_7367_) as usize);
                    crate::leanh::lean_inc_ref(v_e_7368_);
                    v___f_7386_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__1___boxed as *mut core::ffi::c_void, 13, 7);
                    crate::leanh::lean_closure_set(v___f_7386_, 0, v___x_7382_);
                    crate::leanh::lean_closure_set(v___f_7386_, 1, v_pre_7363_);
                    crate::leanh::lean_closure_set(v___f_7386_, 2, v_e_7368_);
                    crate::leanh::lean_closure_set(v___f_7386_, 3, v_post_7364_);
                    crate::leanh::lean_closure_set(v___f_7386_, 4, v___x_7383_);
                    crate::leanh::lean_closure_set(v___f_7386_, 5, v___x_7384_);
                    crate::leanh::lean_closure_set(v___f_7386_, 6, v___x_7385_);
                    v___x_7387_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v___f_7386_, v_a_7369_, v___y_7370_, v___y_7371_, v___y_7372_, v___y_7373_);
                    if crate::leanh::lean_obj_tag(v___x_7387_) == 0 {
                        v_a_7388_ = crate::leanh::lean_ctor_get(v___x_7387_, 0);
                        crate::leanh::lean_inc_n(v_a_7388_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_7387_, 1);
                        crate::leanh::lean_inc(v_a_7369_);
                        v___f_7389_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                        crate::leanh::lean_closure_set(v___f_7389_, 0, v_a_7369_);
                        crate::leanh::lean_closure_set(v___f_7389_, 1, v_e_7368_);
                        crate::leanh::lean_closure_set(v___f_7389_, 2, v_a_7388_);
                        v___x_7390_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___lam__0(crate::leanh::lean_box(0), v___f_7389_, v___y_7370_, v___y_7371_, v___y_7372_, v___y_7373_);
                        if crate::leanh::lean_obj_tag(v___x_7390_) == 0 {
                            v_isSharedCheck_7397_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7390_)) as u8;
                            if v_isSharedCheck_7397_ == 0 {
                                v_unused_7398_ = crate::leanh::lean_ctor_get(v___x_7390_, 0);
                                crate::leanh::lean_dec(v_unused_7398_);
                                v___x_7392_ = v___x_7390_;
                                v_isShared_7393_ = v_isSharedCheck_7397_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7390_);
                                v___x_7392_ = crate::leanh::lean_box(0);
                                v_isShared_7393_ = v_isSharedCheck_7397_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7388_);
                            v_a_7399_ = crate::leanh::lean_ctor_get(v___x_7390_, 0);
                            v_isSharedCheck_7406_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7390_)) as u8;
                            if v_isSharedCheck_7406_ == 0 {
                                v___x_7401_ = v___x_7390_;
                                v_isShared_7402_ = v_isSharedCheck_7406_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7399_);
                                crate::leanh::lean_dec(v___x_7390_);
                                v___x_7401_ = crate::leanh::lean_box(0);
                                v_isShared_7402_ = v_isSharedCheck_7406_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7368_);
                        return v___x_7387_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7368_);
                    crate::leanh::lean_dec_ref(v_post_7364_);
                    crate::leanh::lean_dec_ref(v_pre_7363_);
                    v_val_7407_ = crate::leanh::lean_ctor_get(v___x_7381_, 0);
                    crate::leanh::lean_inc(v_val_7407_);
                    crate::leanh::lean_dec_ref_known(v___x_7381_, 1);
                    if v_isShared_7380_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7379_, 0, v_val_7407_);
                        v___x_7409_ = v___x_7379_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7410_, 0, v_val_7407_);
                        v___x_7409_ = v_reuseFailAlloc_7410_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7392_, 0, v_a_7388_);
                    v___x_7395_ = v___x_7392_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7396_, 0, v_a_7388_);
                    v___x_7395_ = v_reuseFailAlloc_7396_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7395_;
            }
            4 => {
                if v_isShared_7402_ == 0 {
                    v___x_7404_ = v___x_7401_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7405_, 0, v_a_7399_);
                    v___x_7404_ = v_reuseFailAlloc_7405_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7404_;
            }
            6 => {
                return v___x_7409_;
            }
            7 => {
                if v_isShared_7415_ == 0 {
                    v___x_7417_ = v___x_7414_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7418_, 0, v_a_7412_);
                    v___x_7417_ = v_reuseFailAlloc_7418_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed(
    mut v_fvars_7420_: *mut crate::leanh::LeanObject,
    mut v_pre_7421_: *mut crate::leanh::LeanObject,
    mut v_post_7422_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7423_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7424_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7425_: *mut crate::leanh::LeanObject,
    mut v_body_7426_: *mut crate::leanh::LeanObject,
    mut v_x_7427_: *mut crate::leanh::LeanObject,
    mut v___y_7428_: *mut crate::leanh::LeanObject,
    mut v___y_7429_: *mut crate::leanh::LeanObject,
    mut v___y_7430_: *mut crate::leanh::LeanObject,
    mut v___y_7431_: *mut crate::leanh::LeanObject,
    mut v___y_7432_: *mut crate::leanh::LeanObject,
    mut v___y_7433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7434_: u8 = 0;
    let mut v_skipConstInApp_boxed_7435_: u8 = 0;
    let mut v_skipInstances_boxed_7436_: u8 = 0;
    let mut v_res_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7434_ = (crate::leanh::lean_unbox(v_usedLetOnly_7423_) as u8);
    v_skipConstInApp_boxed_7435_ = (crate::leanh::lean_unbox(v_skipConstInApp_7424_) as u8);
    v_skipInstances_boxed_7436_ = (crate::leanh::lean_unbox(v_skipInstances_7425_) as u8);
    v_res_7437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(v_fvars_7420_, v_pre_7421_, v_post_7422_, v_usedLetOnly_boxed_7434_, v_skipConstInApp_boxed_7435_, v_skipInstances_boxed_7436_, v_body_7426_, v_x_7427_, v___y_7428_, v___y_7429_, v___y_7430_, v___y_7431_, v___y_7432_);
    crate::leanh::lean_dec(v___y_7432_);
    crate::leanh::lean_dec_ref(v___y_7431_);
    crate::leanh::lean_dec(v___y_7430_);
    crate::leanh::lean_dec_ref(v___y_7429_);
    crate::leanh::lean_dec(v___y_7428_);
    return v_res_7437_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(
    mut v_pre_7438_: *mut crate::leanh::LeanObject,
    mut v_post_7439_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7440_: u8,
    mut v_skipConstInApp_7441_: u8,
    mut v_skipInstances_7442_: u8,
    mut v_fvars_7443_: *mut crate::leanh::LeanObject,
    mut v_e_7444_: *mut crate::leanh::LeanObject,
    mut v_a_7445_: *mut crate::leanh::LeanObject,
    mut v___y_7446_: *mut crate::leanh::LeanObject,
    mut v___y_7447_: *mut crate::leanh::LeanObject,
    mut v___y_7448_: *mut crate::leanh::LeanObject,
    mut v___y_7449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_7444_) == 7 {
        let mut v_binderName_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_7454_: u8 = 0;
        let mut v___x_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_7451_ = crate::leanh::lean_ctor_get(v_e_7444_, 0);
        crate::leanh::lean_inc(v_binderName_7451_);
        v_binderType_7452_ = crate::leanh::lean_ctor_get(v_e_7444_, 1);
        crate::leanh::lean_inc_ref(v_binderType_7452_);
        v_body_7453_ = crate::leanh::lean_ctor_get(v_e_7444_, 2);
        crate::leanh::lean_inc_ref(v_body_7453_);
        v_binderInfo_7454_ = crate::leanh::lean_ctor_get_uint8(
            v_e_7444_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_e_7444_, 3);
        v___x_7455_ = lean_expr_instantiate_rev(v_binderType_7452_, v_fvars_7443_);
        crate::leanh::lean_dec_ref(v_binderType_7452_);
        crate::leanh::lean_inc_ref(v_post_7439_);
        crate::leanh::lean_inc_ref(v_pre_7438_);
        v___x_7456_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7438_, v_post_7439_, v_usedLetOnly_7440_, v_skipConstInApp_7441_, v_skipInstances_7442_, v___x_7455_, v_a_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
        if crate::leanh::lean_obj_tag(v___x_7456_) == 0 {
            let mut v_a_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7462_: u8 = 0;
            let mut v___x_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7457_ = crate::leanh::lean_ctor_get(v___x_7456_, 0);
            crate::leanh::lean_inc(v_a_7457_);
            crate::leanh::lean_dec_ref_known(v___x_7456_, 1);
            v___x_7458_ = crate::leanh::lean_box((v_usedLetOnly_7440_) as usize);
            v___x_7459_ = crate::leanh::lean_box((v_skipConstInApp_7441_) as usize);
            v___x_7460_ = crate::leanh::lean_box((v_skipInstances_7442_) as usize);
            v___f_7461_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
            crate::leanh::lean_closure_set(v___f_7461_, 0, v_fvars_7443_);
            crate::leanh::lean_closure_set(v___f_7461_, 1, v_pre_7438_);
            crate::leanh::lean_closure_set(v___f_7461_, 2, v_post_7439_);
            crate::leanh::lean_closure_set(v___f_7461_, 3, v___x_7458_);
            crate::leanh::lean_closure_set(v___f_7461_, 4, v___x_7459_);
            crate::leanh::lean_closure_set(v___f_7461_, 5, v___x_7460_);
            crate::leanh::lean_closure_set(v___f_7461_, 6, v_body_7453_);
            v___x_7462_ = 0;
            v___x_7463_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_binderName_7451_, v_binderInfo_7454_, v_a_7457_, v___f_7461_, v___x_7462_, v_a_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
            return v___x_7463_;
        } else {
            crate::leanh::lean_dec_ref(v_body_7453_);
            crate::leanh::lean_dec(v_binderName_7451_);
            crate::leanh::lean_dec_ref(v_fvars_7443_);
            crate::leanh::lean_dec_ref(v_post_7439_);
            crate::leanh::lean_dec_ref(v_pre_7438_);
            return v___x_7456_;
        }
    } else {
        let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7464_ = lean_expr_instantiate_rev(v_e_7444_, v_fvars_7443_);
        crate::leanh::lean_dec_ref(v_e_7444_);
        crate::leanh::lean_inc_ref(v_post_7439_);
        crate::leanh::lean_inc_ref(v_pre_7438_);
        v___x_7465_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7438_, v_post_7439_, v_usedLetOnly_7440_, v_skipConstInApp_7441_, v_skipInstances_7442_, v___x_7464_, v_a_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
        if crate::leanh::lean_obj_tag(v___x_7465_) == 0 {
            let mut v_a_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7467_: u8 = 0;
            let mut v___x_7468_: u8 = 0;
            let mut v___x_7469_: u8 = 0;
            let mut v___x_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_7466_ = crate::leanh::lean_ctor_get(v___x_7465_, 0);
            crate::leanh::lean_inc(v_a_7466_);
            crate::leanh::lean_dec_ref_known(v___x_7465_, 1);
            v___x_7467_ = 0;
            v___x_7468_ = 1;
            v___x_7469_ = 1;
            v___x_7470_ = l_Lean_Meta_mkForallFVars(
                v_fvars_7443_,
                v_a_7466_,
                v___x_7467_,
                v_usedLetOnly_7440_,
                v___x_7468_,
                v___x_7469_,
                v___y_7446_,
                v___y_7447_,
                v___y_7448_,
                v___y_7449_,
            );
            crate::leanh::lean_dec_ref(v_fvars_7443_);
            if crate::leanh::lean_obj_tag(v___x_7470_) == 0 {
                let mut v_a_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_7471_ = crate::leanh::lean_ctor_get(v___x_7470_, 0);
                crate::leanh::lean_inc(v_a_7471_);
                crate::leanh::lean_dec_ref_known(v___x_7470_, 1);
                v___x_7472_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7438_, v_post_7439_, v_usedLetOnly_7440_, v_skipConstInApp_7441_, v_skipInstances_7442_, v_a_7471_, v_a_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_);
                return v___x_7472_;
            } else {
                crate::leanh::lean_dec_ref(v_post_7439_);
                crate::leanh::lean_dec_ref(v_pre_7438_);
                return v___x_7470_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_fvars_7443_);
            crate::leanh::lean_dec_ref(v_post_7439_);
            crate::leanh::lean_dec_ref(v_pre_7438_);
            return v___x_7465_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___lam__0(
    mut v_fvars_7473_: *mut crate::leanh::LeanObject,
    mut v_pre_7474_: *mut crate::leanh::LeanObject,
    mut v_post_7475_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7476_: u8,
    mut v_skipConstInApp_7477_: u8,
    mut v_skipInstances_7478_: u8,
    mut v_body_7479_: *mut crate::leanh::LeanObject,
    mut v_x_7480_: *mut crate::leanh::LeanObject,
    mut v___y_7481_: *mut crate::leanh::LeanObject,
    mut v___y_7482_: *mut crate::leanh::LeanObject,
    mut v___y_7483_: *mut crate::leanh::LeanObject,
    mut v___y_7484_: *mut crate::leanh::LeanObject,
    mut v___y_7485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7487_ = lean_array_push(v_fvars_7473_, v_x_7480_);
    v___x_7488_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_7474_, v_post_7475_, v_usedLetOnly_7476_, v_skipConstInApp_7477_, v_skipInstances_7478_, v___x_7487_, v_body_7479_, v___y_7481_, v___y_7482_, v___y_7483_, v___y_7484_, v___y_7485_);
    return v___x_7488_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3___boxed(
    mut v_pre_7489_: *mut crate::leanh::LeanObject,
    mut v_post_7490_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7491_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7492_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7493_: *mut crate::leanh::LeanObject,
    mut v_e_7494_: *mut crate::leanh::LeanObject,
    mut v_a_7495_: *mut crate::leanh::LeanObject,
    mut v___y_7496_: *mut crate::leanh::LeanObject,
    mut v___y_7497_: *mut crate::leanh::LeanObject,
    mut v___y_7498_: *mut crate::leanh::LeanObject,
    mut v___y_7499_: *mut crate::leanh::LeanObject,
    mut v___y_7500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7501_: u8 = 0;
    let mut v_skipConstInApp_boxed_7502_: u8 = 0;
    let mut v_skipInstances_boxed_7503_: u8 = 0;
    let mut v_res_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7501_ = (crate::leanh::lean_unbox(v_usedLetOnly_7491_) as u8);
    v_skipConstInApp_boxed_7502_ = (crate::leanh::lean_unbox(v_skipConstInApp_7492_) as u8);
    v_skipInstances_boxed_7503_ = (crate::leanh::lean_unbox(v_skipInstances_7493_) as u8);
    v_res_7504_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__3(v_pre_7489_, v_post_7490_, v_usedLetOnly_boxed_7501_, v_skipConstInApp_boxed_7502_, v_skipInstances_boxed_7503_, v_e_7494_, v_a_7495_, v___y_7496_, v___y_7497_, v___y_7498_, v___y_7499_);
    crate::leanh::lean_dec(v___y_7499_);
    crate::leanh::lean_dec_ref(v___y_7498_);
    crate::leanh::lean_dec(v___y_7497_);
    crate::leanh::lean_dec_ref(v___y_7496_);
    crate::leanh::lean_dec(v_a_7495_);
    return v_res_7504_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2___boxed(
    mut v_pre_7505_: *mut crate::leanh::LeanObject,
    mut v_post_7506_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7507_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7508_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7509_: *mut crate::leanh::LeanObject,
    mut v_sz_7510_: *mut crate::leanh::LeanObject,
    mut v_i_7511_: *mut crate::leanh::LeanObject,
    mut v_bs_7512_: *mut crate::leanh::LeanObject,
    mut v___y_7513_: *mut crate::leanh::LeanObject,
    mut v___y_7514_: *mut crate::leanh::LeanObject,
    mut v___y_7515_: *mut crate::leanh::LeanObject,
    mut v___y_7516_: *mut crate::leanh::LeanObject,
    mut v___y_7517_: *mut crate::leanh::LeanObject,
    mut v___y_7518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7519_: u8 = 0;
    let mut v_skipConstInApp_boxed_7520_: u8 = 0;
    let mut v_skipInstances_boxed_7521_: u8 = 0;
    let mut v_sz_boxed_7522_: usize = 0;
    let mut v_i_boxed_7523_: usize = 0;
    let mut v_res_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7519_ = (crate::leanh::lean_unbox(v_usedLetOnly_7507_) as u8);
    v_skipConstInApp_boxed_7520_ = (crate::leanh::lean_unbox(v_skipConstInApp_7508_) as u8);
    v_skipInstances_boxed_7521_ = (crate::leanh::lean_unbox(v_skipInstances_7509_) as u8);
    v_sz_boxed_7522_ = crate::leanh::lean_unbox_usize(v_sz_7510_);
    crate::leanh::lean_dec(v_sz_7510_);
    v_i_boxed_7523_ = crate::leanh::lean_unbox_usize(v_i_7511_);
    crate::leanh::lean_dec(v_i_7511_);
    v_res_7524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__2(v_pre_7505_, v_post_7506_, v_usedLetOnly_boxed_7519_, v_skipConstInApp_boxed_7520_, v_skipInstances_boxed_7521_, v_sz_boxed_7522_, v_i_boxed_7523_, v_bs_7512_, v___y_7513_, v___y_7514_, v___y_7515_, v___y_7516_, v___y_7517_);
    crate::leanh::lean_dec(v___y_7517_);
    crate::leanh::lean_dec_ref(v___y_7516_);
    crate::leanh::lean_dec(v___y_7515_);
    crate::leanh::lean_dec_ref(v___y_7514_);
    crate::leanh::lean_dec(v___y_7513_);
    return v_res_7524_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1___boxed(
    mut v_pre_7525_: *mut crate::leanh::LeanObject,
    mut v_post_7526_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7527_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7528_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7529_: *mut crate::leanh::LeanObject,
    mut v_e_7530_: *mut crate::leanh::LeanObject,
    mut v_a_7531_: *mut crate::leanh::LeanObject,
    mut v___y_7532_: *mut crate::leanh::LeanObject,
    mut v___y_7533_: *mut crate::leanh::LeanObject,
    mut v___y_7534_: *mut crate::leanh::LeanObject,
    mut v___y_7535_: *mut crate::leanh::LeanObject,
    mut v___y_7536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7537_: u8 = 0;
    let mut v_skipConstInApp_boxed_7538_: u8 = 0;
    let mut v_skipInstances_boxed_7539_: u8 = 0;
    let mut v_res_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7537_ = (crate::leanh::lean_unbox(v_usedLetOnly_7527_) as u8);
    v_skipConstInApp_boxed_7538_ = (crate::leanh::lean_unbox(v_skipConstInApp_7528_) as u8);
    v_skipInstances_boxed_7539_ = (crate::leanh::lean_unbox(v_skipInstances_7529_) as u8);
    v_res_7540_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7525_, v_post_7526_, v_usedLetOnly_boxed_7537_, v_skipConstInApp_boxed_7538_, v_skipInstances_boxed_7539_, v_e_7530_, v_a_7531_, v___y_7532_, v___y_7533_, v___y_7534_, v___y_7535_);
    crate::leanh::lean_dec(v___y_7535_);
    crate::leanh::lean_dec_ref(v___y_7534_);
    crate::leanh::lean_dec(v___y_7533_);
    crate::leanh::lean_dec_ref(v___y_7532_);
    crate::leanh::lean_dec(v_a_7531_);
    return v_res_7540_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6___boxed(
    mut v_pre_7541_: *mut crate::leanh::LeanObject,
    mut v_post_7542_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7543_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7544_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7545_: *mut crate::leanh::LeanObject,
    mut v_fvars_7546_: *mut crate::leanh::LeanObject,
    mut v_e_7547_: *mut crate::leanh::LeanObject,
    mut v_a_7548_: *mut crate::leanh::LeanObject,
    mut v___y_7549_: *mut crate::leanh::LeanObject,
    mut v___y_7550_: *mut crate::leanh::LeanObject,
    mut v___y_7551_: *mut crate::leanh::LeanObject,
    mut v___y_7552_: *mut crate::leanh::LeanObject,
    mut v___y_7553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7554_: u8 = 0;
    let mut v_skipConstInApp_boxed_7555_: u8 = 0;
    let mut v_skipInstances_boxed_7556_: u8 = 0;
    let mut v_res_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7554_ = (crate::leanh::lean_unbox(v_usedLetOnly_7543_) as u8);
    v_skipConstInApp_boxed_7555_ = (crate::leanh::lean_unbox(v_skipConstInApp_7544_) as u8);
    v_skipInstances_boxed_7556_ = (crate::leanh::lean_unbox(v_skipInstances_7545_) as u8);
    v_res_7557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6(v_pre_7541_, v_post_7542_, v_usedLetOnly_boxed_7554_, v_skipConstInApp_boxed_7555_, v_skipInstances_boxed_7556_, v_fvars_7546_, v_e_7547_, v_a_7548_, v___y_7549_, v___y_7550_, v___y_7551_, v___y_7552_);
    crate::leanh::lean_dec(v___y_7552_);
    crate::leanh::lean_dec_ref(v___y_7551_);
    crate::leanh::lean_dec(v___y_7550_);
    crate::leanh::lean_dec_ref(v___y_7549_);
    crate::leanh::lean_dec(v_a_7548_);
    return v_res_7557_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7___boxed(
    mut v_pre_7558_: *mut crate::leanh::LeanObject,
    mut v_post_7559_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7560_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7561_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7562_: *mut crate::leanh::LeanObject,
    mut v_fvars_7563_: *mut crate::leanh::LeanObject,
    mut v_e_7564_: *mut crate::leanh::LeanObject,
    mut v_a_7565_: *mut crate::leanh::LeanObject,
    mut v___y_7566_: *mut crate::leanh::LeanObject,
    mut v___y_7567_: *mut crate::leanh::LeanObject,
    mut v___y_7568_: *mut crate::leanh::LeanObject,
    mut v___y_7569_: *mut crate::leanh::LeanObject,
    mut v___y_7570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7571_: u8 = 0;
    let mut v_skipConstInApp_boxed_7572_: u8 = 0;
    let mut v_skipInstances_boxed_7573_: u8 = 0;
    let mut v_res_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7571_ = (crate::leanh::lean_unbox(v_usedLetOnly_7560_) as u8);
    v_skipConstInApp_boxed_7572_ = (crate::leanh::lean_unbox(v_skipConstInApp_7561_) as u8);
    v_skipInstances_boxed_7573_ = (crate::leanh::lean_unbox(v_skipInstances_7562_) as u8);
    v_res_7574_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__7(v_pre_7558_, v_post_7559_, v_usedLetOnly_boxed_7571_, v_skipConstInApp_boxed_7572_, v_skipInstances_boxed_7573_, v_fvars_7563_, v_e_7564_, v_a_7565_, v___y_7566_, v___y_7567_, v___y_7568_, v___y_7569_);
    crate::leanh::lean_dec(v___y_7569_);
    crate::leanh::lean_dec_ref(v___y_7568_);
    crate::leanh::lean_dec(v___y_7567_);
    crate::leanh::lean_dec_ref(v___y_7566_);
    crate::leanh::lean_dec(v_a_7565_);
    return v_res_7574_;
}
pub unsafe fn l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8___boxed(
    mut v_pre_7575_: *mut crate::leanh::LeanObject,
    mut v_post_7576_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7577_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7578_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7579_: *mut crate::leanh::LeanObject,
    mut v_fvars_7580_: *mut crate::leanh::LeanObject,
    mut v_e_7581_: *mut crate::leanh::LeanObject,
    mut v_a_7582_: *mut crate::leanh::LeanObject,
    mut v___y_7583_: *mut crate::leanh::LeanObject,
    mut v___y_7584_: *mut crate::leanh::LeanObject,
    mut v___y_7585_: *mut crate::leanh::LeanObject,
    mut v___y_7586_: *mut crate::leanh::LeanObject,
    mut v___y_7587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7588_: u8 = 0;
    let mut v_skipConstInApp_boxed_7589_: u8 = 0;
    let mut v_skipInstances_boxed_7590_: u8 = 0;
    let mut v_res_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7588_ = (crate::leanh::lean_unbox(v_usedLetOnly_7577_) as u8);
    v_skipConstInApp_boxed_7589_ = (crate::leanh::lean_unbox(v_skipConstInApp_7578_) as u8);
    v_skipInstances_boxed_7590_ = (crate::leanh::lean_unbox(v_skipInstances_7579_) as u8);
    v_res_7591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8(v_pre_7575_, v_post_7576_, v_usedLetOnly_boxed_7588_, v_skipConstInApp_boxed_7589_, v_skipInstances_boxed_7590_, v_fvars_7580_, v_e_7581_, v_a_7582_, v___y_7583_, v___y_7584_, v___y_7585_, v___y_7586_);
    crate::leanh::lean_dec(v___y_7586_);
    crate::leanh::lean_dec_ref(v___y_7585_);
    crate::leanh::lean_dec(v___y_7584_);
    crate::leanh::lean_dec_ref(v___y_7583_);
    crate::leanh::lean_dec(v_a_7582_);
    return v_res_7591_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_upperBound_7592_: *mut crate::leanh::LeanObject,
    mut v___x_7593_: *mut crate::leanh::LeanObject,
    mut v_pre_7594_: *mut crate::leanh::LeanObject,
    mut v_post_7595_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7596_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7597_: *mut crate::leanh::LeanObject,
    mut v_skipInstances_7598_: *mut crate::leanh::LeanObject,
    mut v_a_7599_: *mut crate::leanh::LeanObject,
    mut v_b_7600_: *mut crate::leanh::LeanObject,
    mut v___y_7601_: *mut crate::leanh::LeanObject,
    mut v___y_7602_: *mut crate::leanh::LeanObject,
    mut v___y_7603_: *mut crate::leanh::LeanObject,
    mut v___y_7604_: *mut crate::leanh::LeanObject,
    mut v___y_7605_: *mut crate::leanh::LeanObject,
    mut v___y_7606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7607_: u8 = 0;
    let mut v_skipConstInApp_boxed_7608_: u8 = 0;
    let mut v_skipInstances_boxed_7609_: u8 = 0;
    let mut v_res_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7607_ = (crate::leanh::lean_unbox(v_usedLetOnly_7596_) as u8);
    v_skipConstInApp_boxed_7608_ = (crate::leanh::lean_unbox(v_skipConstInApp_7597_) as u8);
    v_skipInstances_boxed_7609_ = (crate::leanh::lean_unbox(v_skipInstances_7598_) as u8);
    v_res_7610_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_7592_, v___x_7593_, v_pre_7594_, v_post_7595_, v_usedLetOnly_boxed_7607_, v_skipConstInApp_boxed_7608_, v_skipInstances_boxed_7609_, v_a_7599_, v_b_7600_, v___y_7601_, v___y_7602_, v___y_7603_, v___y_7604_, v___y_7605_);
    crate::leanh::lean_dec(v___y_7605_);
    crate::leanh::lean_dec_ref(v___y_7604_);
    crate::leanh::lean_dec(v___y_7603_);
    crate::leanh::lean_dec_ref(v___y_7602_);
    crate::leanh::lean_dec(v___y_7601_);
    crate::leanh::lean_dec_ref(v___x_7593_);
    crate::leanh::lean_dec(v_upperBound_7592_);
    return v_res_7610_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9___boxed(
    mut v_skipInstances_7611_: *mut crate::leanh::LeanObject,
    mut v_pre_7612_: *mut crate::leanh::LeanObject,
    mut v_post_7613_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7614_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7615_: *mut crate::leanh::LeanObject,
    mut v_x_7616_: *mut crate::leanh::LeanObject,
    mut v_x_7617_: *mut crate::leanh::LeanObject,
    mut v_x_7618_: *mut crate::leanh::LeanObject,
    mut v___y_7619_: *mut crate::leanh::LeanObject,
    mut v___y_7620_: *mut crate::leanh::LeanObject,
    mut v___y_7621_: *mut crate::leanh::LeanObject,
    mut v___y_7622_: *mut crate::leanh::LeanObject,
    mut v___y_7623_: *mut crate::leanh::LeanObject,
    mut v___y_7624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipInstances_boxed_7625_: u8 = 0;
    let mut v_usedLetOnly_boxed_7626_: u8 = 0;
    let mut v_skipConstInApp_boxed_7627_: u8 = 0;
    let mut v_res_7628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipInstances_boxed_7625_ = (crate::leanh::lean_unbox(v_skipInstances_7611_) as u8);
    v_usedLetOnly_boxed_7626_ = (crate::leanh::lean_unbox(v_usedLetOnly_7614_) as u8);
    v_skipConstInApp_boxed_7627_ = (crate::leanh::lean_unbox(v_skipConstInApp_7615_) as u8);
    v_res_7628_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__9(v_skipInstances_boxed_7625_, v_pre_7612_, v_post_7613_, v_usedLetOnly_boxed_7626_, v_skipConstInApp_boxed_7627_, v_x_7616_, v_x_7617_, v_x_7618_, v___y_7619_, v___y_7620_, v___y_7621_, v___y_7622_, v___y_7623_);
    crate::leanh::lean_dec(v___y_7623_);
    crate::leanh::lean_dec_ref(v___y_7622_);
    crate::leanh::lean_dec(v___y_7621_);
    crate::leanh::lean_dec_ref(v___y_7620_);
    crate::leanh::lean_dec(v___y_7619_);
    return v_res_7628_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7629_ = crate::leanh::lean_box(0);
    v___x_7630_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_7631_ = lean_mk_array(v___x_7630_, v___x_7629_);
    return v___x_7631_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7632_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__0,
    );
    v___x_7633_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7634_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7634_, 0, v___x_7633_);
    crate::leanh::lean_ctor_set(v___x_7634_, 1, v___x_7632_);
    return v___x_7634_;
}
pub unsafe fn _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7635_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1_once
        ),
        _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__1,
    );
    v___x_7636_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_7636_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_7636_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_7636_, 2, v___x_7635_);
    return v___x_7636_;
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(
    mut v_input_7637_: *mut crate::leanh::LeanObject,
    mut v_pre_7638_: *mut crate::leanh::LeanObject,
    mut v_post_7639_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7640_: u8,
    mut v_skipConstInApp_7641_: u8,
    mut v___y_7642_: *mut crate::leanh::LeanObject,
    mut v___y_7643_: *mut crate::leanh::LeanObject,
    mut v___y_7644_: *mut crate::leanh::LeanObject,
    mut v___y_7645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: u8 = 0;
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7657_: u8 = 0;
    let mut v___x_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7661_: u8 = 0;
    let mut v_unused_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7647_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2_once), _init_l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___closed__2);
                v___x_7648_ =
                    l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(
                        crate::leanh::lean_box(0),
                        v___x_7647_,
                        v___y_7642_,
                        v___y_7643_,
                        v___y_7644_,
                        v___y_7645_,
                    );
                v_a_7649_ = crate::leanh::lean_ctor_get(v___x_7648_, 0);
                crate::leanh::lean_inc(v_a_7649_);
                crate::leanh::lean_dec_ref(v___x_7648_);
                v___x_7650_ = 0;
                v___x_7651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1(v_pre_7638_, v_post_7639_, v_usedLetOnly_7640_, v_skipConstInApp_7641_, v___x_7650_, v_input_7637_, v_a_7649_, v___y_7642_, v___y_7643_, v___y_7644_, v___y_7645_);
                if crate::leanh::lean_obj_tag(v___x_7651_) == 0 {
                    v_a_7652_ = crate::leanh::lean_ctor_get(v___x_7651_, 0);
                    crate::leanh::lean_inc(v_a_7652_);
                    crate::leanh::lean_dec_ref_known(v___x_7651_, 1);
                    v___x_7653_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_7653_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_7653_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_7653_, 2, v_a_7649_);
                    v___x_7654_ =
                        l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___lam__0(
                            crate::leanh::lean_box(0),
                            v___x_7653_,
                            v___y_7642_,
                            v___y_7643_,
                            v___y_7644_,
                            v___y_7645_,
                        );
                    v_isSharedCheck_7661_ = (!crate::leanh::lean_is_exclusive(v___x_7654_)) as u8;
                    if v_isSharedCheck_7661_ == 0 {
                        v_unused_7662_ = crate::leanh::lean_ctor_get(v___x_7654_, 0);
                        crate::leanh::lean_dec(v_unused_7662_);
                        v___x_7656_ = v___x_7654_;
                        v_isShared_7657_ = v_isSharedCheck_7661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7654_);
                        v___x_7656_ = crate::leanh::lean_box(0);
                        v_isShared_7657_ = v_isSharedCheck_7661_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7649_);
                    return v___x_7651_;
                }
            }
            1 => {
                if v_isShared_7657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7656_, 0, v_a_7652_);
                    v___x_7659_ = v___x_7656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7660_, 0, v_a_7652_);
                    v___x_7659_ = v_reuseFailAlloc_7660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1___boxed(
    mut v_input_7663_: *mut crate::leanh::LeanObject,
    mut v_pre_7664_: *mut crate::leanh::LeanObject,
    mut v_post_7665_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7666_: *mut crate::leanh::LeanObject,
    mut v_skipConstInApp_7667_: *mut crate::leanh::LeanObject,
    mut v___y_7668_: *mut crate::leanh::LeanObject,
    mut v___y_7669_: *mut crate::leanh::LeanObject,
    mut v___y_7670_: *mut crate::leanh::LeanObject,
    mut v___y_7671_: *mut crate::leanh::LeanObject,
    mut v___y_7672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_7673_: u8 = 0;
    let mut v_skipConstInApp_boxed_7674_: u8 = 0;
    let mut v_res_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7673_ = (crate::leanh::lean_unbox(v_usedLetOnly_7666_) as u8);
    v_skipConstInApp_boxed_7674_ = (crate::leanh::lean_unbox(v_skipConstInApp_7667_) as u8);
    v_res_7675_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(
        v_input_7663_,
        v_pre_7664_,
        v_post_7665_,
        v_usedLetOnly_boxed_7673_,
        v_skipConstInApp_boxed_7674_,
        v___y_7668_,
        v___y_7669_,
        v___y_7670_,
        v___y_7671_,
    );
    crate::leanh::lean_dec(v___y_7671_);
    crate::leanh::lean_dec_ref(v___y_7670_);
    crate::leanh::lean_dec(v___y_7669_);
    crate::leanh::lean_dec_ref(v___y_7668_);
    return v_res_7675_;
}
pub unsafe fn l_Lean_Meta_etaStructReduce(
    mut v_e_7677_: *mut crate::leanh::LeanObject,
    mut v_p_7678_: *mut crate::leanh::LeanObject,
    mut v_a_7679_: *mut crate::leanh::LeanObject,
    mut v_a_7680_: *mut crate::leanh::LeanObject,
    mut v_a_7681_: *mut crate::leanh::LeanObject,
    mut v_a_7682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: u8 = 0;
    let mut v___x_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7684_ = l_Lean_instantiateMVars___at___00Lean_Meta_etaStructReduce_spec__0___redArg(
        v_e_7677_, v_a_7680_,
    );
    v_a_7685_ = crate::leanh::lean_ctor_get(v___x_7684_, 0);
    crate::leanh::lean_inc(v_a_7685_);
    crate::leanh::lean_dec_ref(v___x_7684_);
    v___f_7686_ = l_Lean_Meta_etaStructReduce___closed__0;
    v___f_7687_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_etaStructReduce___lam__1___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7687_, 0, v_p_7678_);
    v___x_7688_ = 0;
    v___x_7689_ = l_Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1(
        v_a_7685_,
        v___f_7686_,
        v___f_7687_,
        v___x_7688_,
        v___x_7688_,
        v_a_7679_,
        v_a_7680_,
        v_a_7681_,
        v_a_7682_,
    );
    return v___x_7689_;
}
pub unsafe fn l_Lean_Meta_etaStructReduce___boxed(
    mut v_e_7690_: *mut crate::leanh::LeanObject,
    mut v_p_7691_: *mut crate::leanh::LeanObject,
    mut v_a_7692_: *mut crate::leanh::LeanObject,
    mut v_a_7693_: *mut crate::leanh::LeanObject,
    mut v_a_7694_: *mut crate::leanh::LeanObject,
    mut v_a_7695_: *mut crate::leanh::LeanObject,
    mut v_a_7696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7697_ = l_Lean_Meta_etaStructReduce(
        v_e_7690_, v_p_7691_, v_a_7692_, v_a_7693_, v_a_7694_, v_a_7695_,
    );
    crate::leanh::lean_dec(v_a_7695_);
    crate::leanh::lean_dec_ref(v_a_7694_);
    crate::leanh::lean_dec(v_a_7693_);
    crate::leanh::lean_dec_ref(v_a_7692_);
    return v_res_7697_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(
    mut v_upperBound_7698_: *mut crate::leanh::LeanObject,
    mut v___x_7699_: *mut crate::leanh::LeanObject,
    mut v_pre_7700_: *mut crate::leanh::LeanObject,
    mut v_post_7701_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_7702_: u8,
    mut v_skipConstInApp_7703_: u8,
    mut v_skipInstances_7704_: u8,
    mut v___x_7705_: *mut crate::leanh::LeanObject,
    mut v_inst_7706_: *mut crate::leanh::LeanObject,
    mut v_R_7707_: *mut crate::leanh::LeanObject,
    mut v_a_7708_: *mut crate::leanh::LeanObject,
    mut v_b_7709_: *mut crate::leanh::LeanObject,
    mut v_c_7710_: *mut crate::leanh::LeanObject,
    mut v___y_7711_: *mut crate::leanh::LeanObject,
    mut v___y_7712_: *mut crate::leanh::LeanObject,
    mut v___y_7713_: *mut crate::leanh::LeanObject,
    mut v___y_7714_: *mut crate::leanh::LeanObject,
    mut v___y_7715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___redArg(v_upperBound_7698_, v___x_7699_, v_pre_7700_, v_post_7701_, v_usedLetOnly_7702_, v_skipConstInApp_7703_, v_skipInstances_7704_, v_a_7708_, v_b_7709_, v___y_7711_, v___y_7712_, v___y_7713_, v___y_7714_, v___y_7715_);
    return v___x_7717_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_7718_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_7719_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_pre_7720_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_post_7721_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_usedLetOnly_7722_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_skipConstInApp_7723_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_skipInstances_7724_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_7725_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_7726_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_R_7727_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_7728_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_b_7729_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_c_7730_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_7731_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_7732_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_7733_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7734_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_7735_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_7736_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_usedLetOnly_boxed_7737_: u8 = 0;
    let mut v_skipConstInApp_boxed_7738_: u8 = 0;
    let mut v_skipInstances_boxed_7739_: u8 = 0;
    let mut v_res_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_7737_ = (crate::leanh::lean_unbox(v_usedLetOnly_7722_) as u8);
    v_skipConstInApp_boxed_7738_ = (crate::leanh::lean_unbox(v_skipConstInApp_7723_) as u8);
    v_skipInstances_boxed_7739_ = (crate::leanh::lean_unbox(v_skipInstances_7724_) as u8);
    v_res_7740_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__4(v_upperBound_7718_, v___x_7719_, v_pre_7720_, v_post_7721_, v_usedLetOnly_boxed_7737_, v_skipConstInApp_boxed_7738_, v_skipInstances_boxed_7739_, v___x_7725_, v_inst_7726_, v_R_7727_, v_a_7728_, v_b_7729_, v_c_7730_, v___y_7731_, v___y_7732_, v___y_7733_, v___y_7734_, v___y_7735_);
    crate::leanh::lean_dec(v___y_7735_);
    crate::leanh::lean_dec_ref(v___y_7734_);
    crate::leanh::lean_dec(v___y_7733_);
    crate::leanh::lean_dec_ref(v___y_7732_);
    crate::leanh::lean_dec(v___y_7731_);
    crate::leanh::lean_dec(v___x_7725_);
    crate::leanh::lean_dec_ref(v___x_7719_);
    crate::leanh::lean_dec(v_upperBound_7718_);
    return v_res_7740_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(
    mut v_00_u03b2_7741_: *mut crate::leanh::LeanObject,
    mut v_m_7742_: *mut crate::leanh::LeanObject,
    mut v_a_7743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___redArg(v_m_7742_, v_a_7743_);
    return v___x_7744_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5___boxed(
    mut v_00_u03b2_7745_: *mut crate::leanh::LeanObject,
    mut v_m_7746_: *mut crate::leanh::LeanObject,
    mut v_a_7747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5(v_00_u03b2_7745_, v_m_7746_, v_a_7747_);
    crate::leanh::lean_dec_ref(v_a_7747_);
    crate::leanh::lean_dec_ref(v_m_7746_);
    return v_res_7748_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(
    mut v_00_u03b1_7749_: *mut crate::leanh::LeanObject,
    mut v_name_7750_: *mut crate::leanh::LeanObject,
    mut v_bi_7751_: u8,
    mut v_type_7752_: *mut crate::leanh::LeanObject,
    mut v_k_7753_: *mut crate::leanh::LeanObject,
    mut v_kind_7754_: u8,
    mut v___y_7755_: *mut crate::leanh::LeanObject,
    mut v___y_7756_: *mut crate::leanh::LeanObject,
    mut v___y_7757_: *mut crate::leanh::LeanObject,
    mut v___y_7758_: *mut crate::leanh::LeanObject,
    mut v___y_7759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7761_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___redArg(v_name_7750_, v_bi_7751_, v_type_7752_, v_k_7753_, v_kind_7754_, v___y_7755_, v___y_7756_, v___y_7757_, v___y_7758_, v___y_7759_);
    return v___x_7761_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8___boxed(
    mut v_00_u03b1_7762_: *mut crate::leanh::LeanObject,
    mut v_name_7763_: *mut crate::leanh::LeanObject,
    mut v_bi_7764_: *mut crate::leanh::LeanObject,
    mut v_type_7765_: *mut crate::leanh::LeanObject,
    mut v_k_7766_: *mut crate::leanh::LeanObject,
    mut v_kind_7767_: *mut crate::leanh::LeanObject,
    mut v___y_7768_: *mut crate::leanh::LeanObject,
    mut v___y_7769_: *mut crate::leanh::LeanObject,
    mut v___y_7770_: *mut crate::leanh::LeanObject,
    mut v___y_7771_: *mut crate::leanh::LeanObject,
    mut v___y_7772_: *mut crate::leanh::LeanObject,
    mut v___y_7773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_7774_: u8 = 0;
    let mut v_kind_boxed_7775_: u8 = 0;
    let mut v_res_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_7774_ = (crate::leanh::lean_unbox(v_bi_7764_) as u8);
    v_kind_boxed_7775_ = (crate::leanh::lean_unbox(v_kind_7767_) as u8);
    v_res_7776_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__6_spec__8(v_00_u03b1_7762_, v_name_7763_, v_bi_boxed_7774_, v_type_7765_, v_k_7766_, v_kind_boxed_7775_, v___y_7768_, v___y_7769_, v___y_7770_, v___y_7771_, v___y_7772_);
    crate::leanh::lean_dec(v___y_7772_);
    crate::leanh::lean_dec_ref(v___y_7771_);
    crate::leanh::lean_dec(v___y_7770_);
    crate::leanh::lean_dec_ref(v___y_7769_);
    crate::leanh::lean_dec(v___y_7768_);
    return v_res_7776_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(
    mut v_00_u03b1_7777_: *mut crate::leanh::LeanObject,
    mut v_name_7778_: *mut crate::leanh::LeanObject,
    mut v_type_7779_: *mut crate::leanh::LeanObject,
    mut v_val_7780_: *mut crate::leanh::LeanObject,
    mut v_k_7781_: *mut crate::leanh::LeanObject,
    mut v_nondep_7782_: u8,
    mut v_kind_7783_: u8,
    mut v___y_7784_: *mut crate::leanh::LeanObject,
    mut v___y_7785_: *mut crate::leanh::LeanObject,
    mut v___y_7786_: *mut crate::leanh::LeanObject,
    mut v___y_7787_: *mut crate::leanh::LeanObject,
    mut v___y_7788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7790_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___redArg(v_name_7778_, v_type_7779_, v_val_7780_, v_k_7781_, v_nondep_7782_, v_kind_7783_, v___y_7784_, v___y_7785_, v___y_7786_, v___y_7787_, v___y_7788_);
    return v___x_7790_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11___boxed(
    mut v_00_u03b1_7791_: *mut crate::leanh::LeanObject,
    mut v_name_7792_: *mut crate::leanh::LeanObject,
    mut v_type_7793_: *mut crate::leanh::LeanObject,
    mut v_val_7794_: *mut crate::leanh::LeanObject,
    mut v_k_7795_: *mut crate::leanh::LeanObject,
    mut v_nondep_7796_: *mut crate::leanh::LeanObject,
    mut v_kind_7797_: *mut crate::leanh::LeanObject,
    mut v___y_7798_: *mut crate::leanh::LeanObject,
    mut v___y_7799_: *mut crate::leanh::LeanObject,
    mut v___y_7800_: *mut crate::leanh::LeanObject,
    mut v___y_7801_: *mut crate::leanh::LeanObject,
    mut v___y_7802_: *mut crate::leanh::LeanObject,
    mut v___y_7803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_7804_: u8 = 0;
    let mut v_kind_boxed_7805_: u8 = 0;
    let mut v_res_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_7804_ = (crate::leanh::lean_unbox(v_nondep_7796_) as u8);
    v_kind_boxed_7805_ = (crate::leanh::lean_unbox(v_kind_7797_) as u8);
    v_res_7806_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__8_spec__11(v_00_u03b1_7791_, v_name_7792_, v_type_7793_, v_val_7794_, v_k_7795_, v_nondep_boxed_7804_, v_kind_boxed_7805_, v___y_7798_, v___y_7799_, v___y_7800_, v___y_7801_, v___y_7802_);
    crate::leanh::lean_dec(v___y_7802_);
    crate::leanh::lean_dec_ref(v___y_7801_);
    crate::leanh::lean_dec(v___y_7800_);
    crate::leanh::lean_dec_ref(v___y_7799_);
    crate::leanh::lean_dec(v___y_7798_);
    return v_res_7806_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(
    mut v_00_u03b1_7807_: *mut crate::leanh::LeanObject,
    mut v_ref_7808_: *mut crate::leanh::LeanObject,
    mut v___y_7809_: *mut crate::leanh::LeanObject,
    mut v___y_7810_: *mut crate::leanh::LeanObject,
    mut v___y_7811_: *mut crate::leanh::LeanObject,
    mut v___y_7812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7814_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___redArg(v_ref_7808_);
    return v___x_7814_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14___boxed(
    mut v_00_u03b1_7815_: *mut crate::leanh::LeanObject,
    mut v_ref_7816_: *mut crate::leanh::LeanObject,
    mut v___y_7817_: *mut crate::leanh::LeanObject,
    mut v___y_7818_: *mut crate::leanh::LeanObject,
    mut v___y_7819_: *mut crate::leanh::LeanObject,
    mut v___y_7820_: *mut crate::leanh::LeanObject,
    mut v___y_7821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7822_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10_spec__14(v_00_u03b1_7815_, v_ref_7816_, v___y_7817_, v___y_7818_, v___y_7819_, v___y_7820_);
    crate::leanh::lean_dec(v___y_7820_);
    crate::leanh::lean_dec_ref(v___y_7819_);
    crate::leanh::lean_dec(v___y_7818_);
    crate::leanh::lean_dec_ref(v___y_7817_);
    return v_res_7822_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(
    mut v_00_u03b1_7823_: *mut crate::leanh::LeanObject,
    mut v_x_7824_: *mut crate::leanh::LeanObject,
    mut v___y_7825_: *mut crate::leanh::LeanObject,
    mut v___y_7826_: *mut crate::leanh::LeanObject,
    mut v___y_7827_: *mut crate::leanh::LeanObject,
    mut v___y_7828_: *mut crate::leanh::LeanObject,
    mut v___y_7829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7831_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___redArg(v_x_7824_, v___y_7825_, v___y_7826_, v___y_7827_, v___y_7828_, v___y_7829_);
    return v___x_7831_;
}
pub unsafe fn l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10___boxed(
    mut v_00_u03b1_7832_: *mut crate::leanh::LeanObject,
    mut v_x_7833_: *mut crate::leanh::LeanObject,
    mut v___y_7834_: *mut crate::leanh::LeanObject,
    mut v___y_7835_: *mut crate::leanh::LeanObject,
    mut v___y_7836_: *mut crate::leanh::LeanObject,
    mut v___y_7837_: *mut crate::leanh::LeanObject,
    mut v___y_7838_: *mut crate::leanh::LeanObject,
    mut v___y_7839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7840_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__10(v_00_u03b1_7832_, v_x_7833_, v___y_7834_, v___y_7835_, v___y_7836_, v___y_7837_, v___y_7838_);
    crate::leanh::lean_dec(v___y_7838_);
    crate::leanh::lean_dec_ref(v___y_7837_);
    crate::leanh::lean_dec(v___y_7836_);
    crate::leanh::lean_dec_ref(v___y_7835_);
    crate::leanh::lean_dec(v___y_7834_);
    return v_res_7840_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11(
    mut v_00_u03b2_7841_: *mut crate::leanh::LeanObject,
    mut v_m_7842_: *mut crate::leanh::LeanObject,
    mut v_a_7843_: *mut crate::leanh::LeanObject,
    mut v_b_7844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7845_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11___redArg(v_m_7842_, v_a_7843_, v_b_7844_);
    return v___x_7845_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(
    mut v_00_u03b2_7846_: *mut crate::leanh::LeanObject,
    mut v_a_7847_: *mut crate::leanh::LeanObject,
    mut v_x_7848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7849_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___redArg(v_a_7847_, v_x_7848_);
    return v___x_7849_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6___boxed(
    mut v_00_u03b2_7850_: *mut crate::leanh::LeanObject,
    mut v_a_7851_: *mut crate::leanh::LeanObject,
    mut v_x_7852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7853_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__5_spec__6(v_00_u03b2_7850_, v_a_7851_, v_x_7852_);
    crate::leanh::lean_dec(v_x_7852_);
    crate::leanh::lean_dec_ref(v_a_7851_);
    return v_res_7853_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(
    mut v_00_u03b2_7854_: *mut crate::leanh::LeanObject,
    mut v_a_7855_: *mut crate::leanh::LeanObject,
    mut v_x_7856_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7857_: u8 = 0;
    v___x_7857_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___redArg(v_a_7855_, v_x_7856_);
    return v___x_7857_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16___boxed(
    mut v_00_u03b2_7858_: *mut crate::leanh::LeanObject,
    mut v_a_7859_: *mut crate::leanh::LeanObject,
    mut v_x_7860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7861_: u8 = 0;
    let mut v_r_7862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__16(v_00_u03b2_7858_, v_a_7859_, v_x_7860_);
    crate::leanh::lean_dec(v_x_7860_);
    crate::leanh::lean_dec_ref(v_a_7859_);
    v_r_7862_ = crate::leanh::lean_box((v_res_7861_) as usize);
    return v_r_7862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17(
    mut v_00_u03b2_7863_: *mut crate::leanh::LeanObject,
    mut v_data_7864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17___redArg(v_data_7864_);
    return v___x_7865_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18(
    mut v_00_u03b2_7866_: *mut crate::leanh::LeanObject,
    mut v_a_7867_: *mut crate::leanh::LeanObject,
    mut v_b_7868_: *mut crate::leanh::LeanObject,
    mut v_x_7869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7870_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__18___redArg(v_a_7867_, v_b_7868_, v_x_7869_);
    return v___x_7870_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18(
    mut v_00_u03b2_7871_: *mut crate::leanh::LeanObject,
    mut v_i_7872_: *mut crate::leanh::LeanObject,
    mut v_source_7873_: *mut crate::leanh::LeanObject,
    mut v_target_7874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7875_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18___redArg(v_i_7872_, v_source_7873_, v_target_7874_);
    return v___x_7875_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19(
    mut v_00_u03b2_7876_: *mut crate::leanh::LeanObject,
    mut v_x_7877_: *mut crate::leanh::LeanObject,
    mut v_x_7878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7879_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_etaStructReduce_spec__1_spec__1_spec__11_spec__17_spec__18_spec__19___redArg(v_x_7877_, v_x_7878_);
    return v___x_7879_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1(
    mut v_binderType_7880_: *mut crate::leanh::LeanObject,
    mut v_inst_7881_: *mut crate::leanh::LeanObject,
    mut v_toBind_7882_: *mut crate::leanh::LeanObject,
    mut v___f_7883_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7885_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_isDefEq___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_7885_, 0, v_____do__lift_7884_);
    crate::leanh::lean_closure_set(v___x_7885_, 1, v_binderType_7880_);
    v___x_7886_ = crate::leanh::lean_apply_2(v_inst_7881_, crate::leanh::lean_box(0), v___x_7885_);
    v___x_7887_ = crate::leanh::lean_apply_4(
        v_toBind_7882_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_7886_,
        v___f_7883_,
    );
    return v___x_7887_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed(
    mut v_toPure_7888_: *mut crate::leanh::LeanObject,
    mut v_usedFields_7889_: *mut crate::leanh::LeanObject,
    mut v_binderName_7890_: *mut crate::leanh::LeanObject,
    mut v_body_7891_: *mut crate::leanh::LeanObject,
    mut v_val_7892_: *mut crate::leanh::LeanObject,
    mut v_inst_7893_: *mut crate::leanh::LeanObject,
    mut v_inst_7894_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_7895_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_469__boxed_7897_: u8 = 0;
    let mut v_res_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_469__boxed_7897_ = (crate::leanh::lean_unbox(v_____do__lift_7896_) as u8);
    v_res_7898_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(v_toPure_7888_, v_usedFields_7889_, v_binderName_7890_, v_body_7891_, v_val_7892_, v_inst_7893_, v_inst_7894_, v_fieldVal_x3f_7895_, v_____do__lift_469__boxed_7897_);
    crate::leanh::lean_dec_ref(v_val_7892_);
    crate::leanh::lean_dec_ref(v_body_7891_);
    return v_res_7898_;
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2(
    mut v_toPure_7899_: *mut crate::leanh::LeanObject,
    mut v_usedFields_7900_: *mut crate::leanh::LeanObject,
    mut v_binderName_7901_: *mut crate::leanh::LeanObject,
    mut v_body_7902_: *mut crate::leanh::LeanObject,
    mut v_inst_7903_: *mut crate::leanh::LeanObject,
    mut v_inst_7904_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_7905_: *mut crate::leanh::LeanObject,
    mut v_binderType_7906_: *mut crate::leanh::LeanObject,
    mut v_toBind_7907_: *mut crate::leanh::LeanObject,
    mut v_____x_7908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_7908_) == 1 {
        let mut v_val_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7909_ = crate::leanh::lean_ctor_get(v_____x_7908_, 0);
        crate::leanh::lean_inc_n(v_val_7909_, 2);
        crate::leanh::lean_dec_ref_known(v_____x_7908_, 1);
        crate::leanh::lean_inc_n(v_inst_7904_, 2);
        v___f_7910_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 8);
        crate::leanh::lean_closure_set(v___f_7910_, 0, v_toPure_7899_);
        crate::leanh::lean_closure_set(v___f_7910_, 1, v_usedFields_7900_);
        crate::leanh::lean_closure_set(v___f_7910_, 2, v_binderName_7901_);
        crate::leanh::lean_closure_set(v___f_7910_, 3, v_body_7902_);
        crate::leanh::lean_closure_set(v___f_7910_, 4, v_val_7909_);
        crate::leanh::lean_closure_set(v___f_7910_, 5, v_inst_7903_);
        crate::leanh::lean_closure_set(v___f_7910_, 6, v_inst_7904_);
        crate::leanh::lean_closure_set(v___f_7910_, 7, v_fieldVal_x3f_7905_);
        crate::leanh::lean_inc(v_toBind_7907_);
        v___f_7911_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
        crate::leanh::lean_closure_set(v___f_7911_, 0, v_binderType_7906_);
        crate::leanh::lean_closure_set(v___f_7911_, 1, v_inst_7904_);
        crate::leanh::lean_closure_set(v___f_7911_, 2, v_toBind_7907_);
        crate::leanh::lean_closure_set(v___f_7911_, 3, v___f_7910_);
        v___x_7912_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        crate::leanh::lean_closure_set(v___x_7912_, 0, v_val_7909_);
        v___x_7913_ =
            crate::leanh::lean_apply_2(v_inst_7904_, crate::leanh::lean_box(0), v___x_7912_);
        v___x_7914_ = crate::leanh::lean_apply_4(
            v_toBind_7907_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_7913_,
            v___f_7911_,
        );
        return v___x_7914_;
    } else {
        let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____x_7908_);
        crate::leanh::lean_dec(v_toBind_7907_);
        crate::leanh::lean_dec_ref(v_binderType_7906_);
        crate::leanh::lean_dec(v_fieldVal_x3f_7905_);
        crate::leanh::lean_dec(v_inst_7904_);
        crate::leanh::lean_dec_ref(v_inst_7903_);
        crate::leanh::lean_dec_ref(v_body_7902_);
        crate::leanh::lean_dec(v_binderName_7901_);
        crate::leanh::lean_dec(v_usedFields_7900_);
        v___x_7915_ = crate::leanh::lean_box(0);
        v___x_7916_ =
            crate::leanh::lean_apply_2(v_toPure_7899_, crate::leanh::lean_box(0), v___x_7915_);
        return v___x_7916_;
    }
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(
    mut v_inst_7920_: *mut crate::leanh::LeanObject,
    mut v_inst_7921_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_7922_: *mut crate::leanh::LeanObject,
    mut v_usedFields_7923_: *mut crate::leanh::LeanObject,
    mut v_e_7924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_7925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7940_: u8 = 0;
    let mut v___x_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: u8 = 0;
    let mut v_arg_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: u8 = 0;
    let mut v___x_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: u8 = 0;
    let mut v___x_7950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7954_: u8 = 0;
    let mut v_unused_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_7925_ = crate::leanh::lean_ctor_get(v_inst_7920_, 0);
                v_toBind_7926_ = crate::leanh::lean_ctor_get(v_inst_7920_, 1);
                v_toPure_7927_ = crate::leanh::lean_ctor_get(v_toApplicative_7925_, 1);
                crate::leanh::lean_inc(v_toPure_7927_);
                if crate::leanh::lean_obj_tag(v_e_7924_) == 6 {
                    crate::leanh::lean_inc_n(v_toBind_7926_, 2);
                    v_binderName_7932_ = crate::leanh::lean_ctor_get(v_e_7924_, 0);
                    crate::leanh::lean_inc_n(v_binderName_7932_, 2);
                    v_binderType_7933_ = crate::leanh::lean_ctor_get(v_e_7924_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_7933_);
                    v_body_7934_ = crate::leanh::lean_ctor_get(v_e_7924_, 2);
                    crate::leanh::lean_inc_ref(v_body_7934_);
                    crate::leanh::lean_dec_ref_known(v_e_7924_, 3);
                    crate::leanh::lean_inc(v_fieldVal_x3f_7922_);
                    v___f_7935_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__2 as *mut core::ffi::c_void, 10, 9);
                    crate::leanh::lean_closure_set(v___f_7935_, 0, v_toPure_7927_);
                    crate::leanh::lean_closure_set(v___f_7935_, 1, v_usedFields_7923_);
                    crate::leanh::lean_closure_set(v___f_7935_, 2, v_binderName_7932_);
                    crate::leanh::lean_closure_set(v___f_7935_, 3, v_body_7934_);
                    crate::leanh::lean_closure_set(v___f_7935_, 4, v_inst_7920_);
                    crate::leanh::lean_closure_set(v___f_7935_, 5, v_inst_7921_);
                    crate::leanh::lean_closure_set(v___f_7935_, 6, v_fieldVal_x3f_7922_);
                    crate::leanh::lean_closure_set(v___f_7935_, 7, v_binderType_7933_);
                    crate::leanh::lean_closure_set(v___f_7935_, 8, v_toBind_7926_);
                    v___x_7936_ =
                        crate::leanh::lean_apply_1(v_fieldVal_x3f_7922_, v_binderName_7932_);
                    v___x_7937_ = crate::leanh::lean_apply_4(
                        v_toBind_7926_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_7936_,
                        v___f_7935_,
                    );
                    return v___x_7937_;
                } else {
                    crate::leanh::lean_dec(v_fieldVal_x3f_7922_);
                    crate::leanh::lean_dec(v_inst_7921_);
                    v_isSharedCheck_7954_ = (!crate::leanh::lean_is_exclusive(v_inst_7920_)) as u8;
                    if v_isSharedCheck_7954_ == 0 {
                        v_unused_7955_ = crate::leanh::lean_ctor_get(v_inst_7920_, 1);
                        crate::leanh::lean_dec(v_unused_7955_);
                        v_unused_7956_ = crate::leanh::lean_ctor_get(v_inst_7920_, 0);
                        crate::leanh::lean_dec(v_unused_7956_);
                        v___x_7939_ = v_inst_7920_;
                        v_isShared_7940_ = v_isSharedCheck_7954_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_inst_7920_);
                        v___x_7939_ = crate::leanh::lean_box(0);
                        v_isShared_7940_ = v_isSharedCheck_7954_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7929_, 0, v_usedFields_7923_);
                crate::leanh::lean_ctor_set(v___x_7929_, 1, v_e_7924_);
                v___x_7930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7930_, 0, v___x_7929_);
                v___x_7931_ = crate::leanh::lean_apply_2(
                    v_toPure_7927_,
                    crate::leanh::lean_box(0),
                    v___x_7930_,
                );
                return v___x_7931_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_e_7924_);
                v___x_7941_ = l_Lean_Expr_cleanupAnnotations(v_e_7924_);
                v___x_7942_ = l_Lean_Expr_isApp(v___x_7941_);
                if v___x_7942_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_7941_);
                    crate::leanh::lean_del_object(v___x_7939_);
                    state = 1;
                    continue;
                } else {
                    v_arg_7943_ = crate::leanh::lean_ctor_get(v___x_7941_, 1);
                    crate::leanh::lean_inc_ref(v_arg_7943_);
                    v___x_7944_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7941_);
                    v___x_7945_ = l_Lean_Expr_isApp(v___x_7944_);
                    if v___x_7945_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_7944_);
                        crate::leanh::lean_dec_ref(v_arg_7943_);
                        crate::leanh::lean_del_object(v___x_7939_);
                        state = 1;
                        continue;
                    } else {
                        v___x_7946_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7944_);
                        v___x_7947_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___closed__1;
                        v___x_7948_ = l_Lean_Expr_isConstOf(v___x_7946_, v___x_7947_);
                        crate::leanh::lean_dec_ref(v___x_7946_);
                        if v___x_7948_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_7943_);
                            crate::leanh::lean_del_object(v___x_7939_);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_e_7924_);
                            if v_isShared_7940_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7939_, 1, v_arg_7943_);
                                crate::leanh::lean_ctor_set(v___x_7939_, 0, v_usedFields_7923_);
                                v___x_7950_ = v___x_7939_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_7953_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_7953_,
                                    0,
                                    v_usedFields_7923_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7953_, 1, v_arg_7943_);
                                v___x_7950_ = v_reuseFailAlloc_7953_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_7951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7951_, 0, v___x_7950_);
                v___x_7952_ = crate::leanh::lean_apply_2(
                    v_toPure_7927_,
                    crate::leanh::lean_box(0),
                    v___x_7951_,
                );
                return v___x_7952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg___lam__0(
    mut v_toPure_7957_: *mut crate::leanh::LeanObject,
    mut v_usedFields_7958_: *mut crate::leanh::LeanObject,
    mut v_binderName_7959_: *mut crate::leanh::LeanObject,
    mut v_body_7960_: *mut crate::leanh::LeanObject,
    mut v_val_7961_: *mut crate::leanh::LeanObject,
    mut v_inst_7962_: *mut crate::leanh::LeanObject,
    mut v_inst_7963_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_7964_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_7965_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_7965_ == 0 {
        let mut v___x_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fieldVal_x3f_7964_);
        crate::leanh::lean_dec(v_inst_7963_);
        crate::leanh::lean_dec_ref(v_inst_7962_);
        crate::leanh::lean_dec(v_binderName_7959_);
        crate::leanh::lean_dec(v_usedFields_7958_);
        v___x_7966_ = crate::leanh::lean_box(0);
        v___x_7967_ =
            crate::leanh::lean_apply_2(v_toPure_7957_, crate::leanh::lean_box(0), v___x_7966_);
        return v___x_7967_;
    } else {
        let mut v___x_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_7957_);
        v___x_7968_ = l_Lean_NameSet_insert(v_usedFields_7958_, v_binderName_7959_);
        v___x_7969_ = lean_expr_instantiate1(v_body_7960_, v_val_7961_);
        v___x_7970_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_7962_, v_inst_7963_, v_fieldVal_x3f_7964_, v___x_7968_, v___x_7969_);
        return v___x_7970_;
    }
}
pub unsafe fn l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f(
    mut v_m_7971_: *mut crate::leanh::LeanObject,
    mut v_inst_7972_: *mut crate::leanh::LeanObject,
    mut v_inst_7973_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_7974_: *mut crate::leanh::LeanObject,
    mut v_usedFields_7975_: *mut crate::leanh::LeanObject,
    mut v_e_7976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7977_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_7972_, v_inst_7973_, v_fieldVal_x3f_7974_, v_usedFields_7975_, v_e_7976_);
    return v___x_7977_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0(
    mut v_inst_7978_: *mut crate::leanh::LeanObject,
    mut v_inst_7979_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_7980_: *mut crate::leanh::LeanObject,
    mut v_toPure_7981_: *mut crate::leanh::LeanObject,
    mut v_____s_7982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_7983_ = crate::leanh::lean_ctor_get(v_____s_7982_, 0);
    if crate::leanh::lean_obj_tag(v_fst_7983_) == 0 {
        let mut v_snd_7984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_7981_);
        v_snd_7984_ = crate::leanh::lean_ctor_get(v_____s_7982_, 1);
        crate::leanh::lean_inc(v_snd_7984_);
        crate::leanh::lean_dec_ref(v_____s_7982_);
        v___x_7985_ = l_Lean_NameSet_empty;
        v___x_7986_ = l___private_Lean_Meta_Structure_0__Lean_Meta_instantiateStructDefaultValueFn_x3f_go_x3f___redArg(v_inst_7978_, v_inst_7979_, v_fieldVal_x3f_7980_, v___x_7985_, v_snd_7984_);
        return v___x_7986_;
    } else {
        let mut v_val_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_fst_7983_);
        crate::leanh::lean_dec_ref(v_____s_7982_);
        crate::leanh::lean_dec(v_fieldVal_x3f_7980_);
        crate::leanh::lean_dec(v_inst_7979_);
        crate::leanh::lean_dec_ref(v_inst_7978_);
        v_val_7987_ = crate::leanh::lean_ctor_get(v_fst_7983_, 0);
        crate::leanh::lean_inc(v_val_7987_);
        crate::leanh::lean_dec_ref_known(v_fst_7983_, 1);
        v___x_7988_ =
            crate::leanh::lean_apply_2(v_toPure_7981_, crate::leanh::lean_box(0), v_val_7987_);
        return v___x_7988_;
    }
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(
    mut v_body_7989_: *mut crate::leanh::LeanObject,
    mut v_a_7990_: *mut crate::leanh::LeanObject,
    mut v___x_7991_: *mut crate::leanh::LeanObject,
    mut v_toPure_7992_: *mut crate::leanh::LeanObject,
    mut v_____r_7993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7994_ = lean_expr_instantiate1(v_body_7989_, v_a_7990_);
    v___x_7995_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7995_, 0, v___x_7991_);
    crate::leanh::lean_ctor_set(v___x_7995_, 1, v___x_7994_);
    v___x_7996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7996_, 0, v___x_7995_);
    v___x_7997_ =
        crate::leanh::lean_apply_2(v_toPure_7992_, crate::leanh::lean_box(0), v___x_7996_);
    return v___x_7997_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed(
    mut v_body_7998_: *mut crate::leanh::LeanObject,
    mut v_a_7999_: *mut crate::leanh::LeanObject,
    mut v___x_8000_: *mut crate::leanh::LeanObject,
    mut v_toPure_8001_: *mut crate::leanh::LeanObject,
    mut v_____r_8002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8003_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(
        v_body_7998_,
        v_a_7999_,
        v___x_8000_,
        v_toPure_8001_,
        v_____r_8002_,
    );
    crate::leanh::lean_dec_ref(v_a_7999_);
    crate::leanh::lean_dec_ref(v_body_7998_);
    return v_res_8003_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(
    mut v_snd_8006_: *mut crate::leanh::LeanObject,
    mut v_toPure_8007_: *mut crate::leanh::LeanObject,
    mut v___f_8008_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8009_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_8009_ == 0 {
        let mut v___x_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_8008_);
        v___x_8010_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0;
        v___x_8011_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_8011_, 0, v___x_8010_);
        crate::leanh::lean_ctor_set(v___x_8011_, 1, v_snd_8006_);
        v___x_8012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_8012_, 0, v___x_8011_);
        v___x_8013_ =
            crate::leanh::lean_apply_2(v_toPure_8007_, crate::leanh::lean_box(0), v___x_8012_);
        return v___x_8013_;
    } else {
        let mut v___x_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_8007_);
        crate::leanh::lean_dec(v_snd_8006_);
        v___x_8014_ = crate::leanh::lean_box(0);
        v___x_8015_ = crate::leanh::lean_apply_1(v___f_8008_, v___x_8014_);
        return v___x_8015_;
    }
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed(
    mut v_snd_8016_: *mut crate::leanh::LeanObject,
    mut v_toPure_8017_: *mut crate::leanh::LeanObject,
    mut v___f_8018_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_852__boxed_8020_: u8 = 0;
    let mut v_res_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_852__boxed_8020_ = (crate::leanh::lean_unbox(v_____do__lift_8019_) as u8);
    v_res_8021_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2(
        v_snd_8016_,
        v_toPure_8017_,
        v___f_8018_,
        v_____do__lift_852__boxed_8020_,
    );
    return v_res_8021_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3(
    mut v_binderType_8022_: *mut crate::leanh::LeanObject,
    mut v_inst_8023_: *mut crate::leanh::LeanObject,
    mut v_toBind_8024_: *mut crate::leanh::LeanObject,
    mut v___f_8025_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_8026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8027_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_isDefEq___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_8027_, 0, v_____do__lift_8026_);
    crate::leanh::lean_closure_set(v___x_8027_, 1, v_binderType_8022_);
    v___x_8028_ = crate::leanh::lean_apply_2(v_inst_8023_, crate::leanh::lean_box(0), v___x_8027_);
    v___x_8029_ = crate::leanh::lean_apply_4(
        v_toBind_8024_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_8028_,
        v___f_8025_,
    );
    return v___x_8029_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(
    mut v___x_8030_: *mut crate::leanh::LeanObject,
    mut v_toPure_8031_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8032_: *mut crate::leanh::LeanObject,
    mut v___x_8033_: u8,
    mut v_inst_8034_: *mut crate::leanh::LeanObject,
    mut v_toBind_8035_: *mut crate::leanh::LeanObject,
    mut v_a_8036_: *mut crate::leanh::LeanObject,
    mut v_x_8037_: *mut crate::leanh::LeanObject,
    mut v___y_8038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_8039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8042_: u8 = 0;
    let mut v_binderType_8043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_8044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8060_: u8 = 0;
    let mut v_unused_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_8039_ = crate::leanh::lean_ctor_get(v___y_8038_, 1);
                v_isSharedCheck_8060_ = (!crate::leanh::lean_is_exclusive(v___y_8038_)) as u8;
                if v_isSharedCheck_8060_ == 0 {
                    v_unused_8061_ = crate::leanh::lean_ctor_get(v___y_8038_, 0);
                    crate::leanh::lean_dec(v_unused_8061_);
                    v___x_8041_ = v___y_8038_;
                    v_isShared_8042_ = v_isSharedCheck_8060_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_8039_);
                    crate::leanh::lean_dec(v___y_8038_);
                    v___x_8041_ = crate::leanh::lean_box(0);
                    v_isShared_8042_ = v_isSharedCheck_8060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_snd_8039_) == 6 {
                    crate::leanh::lean_del_object(v___x_8041_);
                    v_binderType_8043_ = crate::leanh::lean_ctor_get(v_snd_8039_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_8043_);
                    v_body_8044_ = crate::leanh::lean_ctor_get(v_snd_8039_, 2);
                    crate::leanh::lean_inc(v_toPure_8031_);
                    crate::leanh::lean_inc(v___x_8030_);
                    crate::leanh::lean_inc_ref(v_a_8036_);
                    crate::leanh::lean_inc_ref(v_body_8044_);
                    v___f_8045_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_8045_, 0, v_body_8044_);
                    crate::leanh::lean_closure_set(v___f_8045_, 1, v_a_8036_);
                    crate::leanh::lean_closure_set(v___f_8045_, 2, v___x_8030_);
                    crate::leanh::lean_closure_set(v___f_8045_, 3, v_toPure_8031_);
                    if crate::leanh::lean_obj_tag(v_levels_x3f_8032_) == 0 {
                        if v___x_8033_ == 0 {
                            crate::leanh::lean_inc_ref(v_body_8044_);
                            crate::leanh::lean_dec_ref(v___f_8045_);
                            crate::leanh::lean_dec_ref_known(v_snd_8039_, 3);
                            crate::leanh::lean_dec_ref(v_binderType_8043_);
                            crate::leanh::lean_dec(v_toBind_8035_);
                            crate::leanh::lean_dec(v_inst_8034_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_8030_);
                            v___f_8049_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 3);
                            crate::leanh::lean_closure_set(v___f_8049_, 0, v_snd_8039_);
                            crate::leanh::lean_closure_set(v___f_8049_, 1, v_toPure_8031_);
                            crate::leanh::lean_closure_set(v___f_8049_, 2, v___f_8045_);
                            crate::leanh::lean_inc(v_toBind_8035_);
                            crate::leanh::lean_inc(v_inst_8034_);
                            v___f_8050_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__3
                                    as *mut core::ffi::c_void,
                                5,
                                4,
                            );
                            crate::leanh::lean_closure_set(v___f_8050_, 0, v_binderType_8043_);
                            crate::leanh::lean_closure_set(v___f_8050_, 1, v_inst_8034_);
                            crate::leanh::lean_closure_set(v___f_8050_, 2, v_toBind_8035_);
                            crate::leanh::lean_closure_set(v___f_8050_, 3, v___f_8049_);
                            v___x_8051_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
                                6,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_8051_, 0, v_a_8036_);
                            v___x_8052_ = crate::leanh::lean_apply_2(
                                v_inst_8034_,
                                crate::leanh::lean_box(0),
                                v___x_8051_,
                            );
                            v___x_8053_ = crate::leanh::lean_apply_4(
                                v_toBind_8035_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_8052_,
                                v___f_8050_,
                            );
                            return v___x_8053_;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_body_8044_);
                        crate::leanh::lean_dec_ref(v___f_8045_);
                        crate::leanh::lean_dec_ref_known(v_snd_8039_, 3);
                        crate::leanh::lean_dec_ref(v_binderType_8043_);
                        crate::leanh::lean_dec(v_toBind_8035_);
                        crate::leanh::lean_dec(v_inst_8034_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_8036_);
                    crate::leanh::lean_dec(v_toBind_8035_);
                    crate::leanh::lean_dec(v_inst_8034_);
                    crate::leanh::lean_dec(v___x_8030_);
                    v___x_8054_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__2___closed__0;
                    if v_isShared_8042_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8041_, 0, v___x_8054_);
                        v___x_8056_ = v___x_8041_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 0, v___x_8054_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 1, v_snd_8039_);
                        v___x_8056_ = v_reuseFailAlloc_8059_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8047_ = crate::leanh::lean_box(0);
                v___x_8048_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__1(
                    v_body_8044_,
                    v_a_8036_,
                    v___x_8030_,
                    v_toPure_8031_,
                    v___x_8047_,
                );
                crate::leanh::lean_dec_ref(v_a_8036_);
                crate::leanh::lean_dec_ref(v_body_8044_);
                return v___x_8048_;
            }
            3 => {
                v___x_8057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8057_, 0, v___x_8056_);
                v___x_8058_ = crate::leanh::lean_apply_2(
                    v_toPure_8031_,
                    crate::leanh::lean_box(0),
                    v___x_8057_,
                );
                return v___x_8058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed(
    mut v___x_8062_: *mut crate::leanh::LeanObject,
    mut v_toPure_8063_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8064_: *mut crate::leanh::LeanObject,
    mut v___x_8065_: *mut crate::leanh::LeanObject,
    mut v_inst_8066_: *mut crate::leanh::LeanObject,
    mut v_toBind_8067_: *mut crate::leanh::LeanObject,
    mut v_a_8068_: *mut crate::leanh::LeanObject,
    mut v_x_8069_: *mut crate::leanh::LeanObject,
    mut v___y_8070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_888__boxed_8071_: u8 = 0;
    let mut v_res_8072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888__boxed_8071_ = (crate::leanh::lean_unbox(v___x_8065_) as u8);
    v_res_8072_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4(
        v___x_8062_,
        v_toPure_8063_,
        v_levels_x3f_8064_,
        v___x_888__boxed_8071_,
        v_inst_8066_,
        v_toBind_8067_,
        v_a_8068_,
        v_x_8069_,
        v___y_8070_,
    );
    crate::leanh::lean_dec(v_levels_x3f_8064_);
    return v_res_8072_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(
    mut v_toPure_8073_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8074_: *mut crate::leanh::LeanObject,
    mut v___x_8075_: u8,
    mut v_inst_8076_: *mut crate::leanh::LeanObject,
    mut v_toBind_8077_: *mut crate::leanh::LeanObject,
    mut v_params_8078_: *mut crate::leanh::LeanObject,
    mut v_inst_8079_: *mut crate::leanh::LeanObject,
    mut v___f_8080_: *mut crate::leanh::LeanObject,
    mut v_val_8081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8086_: usize = 0;
    let mut v___x_8087_: usize = 0;
    let mut v___x_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8082_ = crate::leanh::lean_box(0);
    v___x_8083_ = crate::leanh::lean_box((v___x_8075_) as usize);
    crate::leanh::lean_inc(v_toBind_8077_);
    v___f_8084_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_8084_, 0, v___x_8082_);
    crate::leanh::lean_closure_set(v___f_8084_, 1, v_toPure_8073_);
    crate::leanh::lean_closure_set(v___f_8084_, 2, v_levels_x3f_8074_);
    crate::leanh::lean_closure_set(v___f_8084_, 3, v___x_8083_);
    crate::leanh::lean_closure_set(v___f_8084_, 4, v_inst_8076_);
    crate::leanh::lean_closure_set(v___f_8084_, 5, v_toBind_8077_);
    v___x_8085_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8085_, 0, v___x_8082_);
    crate::leanh::lean_ctor_set(v___x_8085_, 1, v_val_8081_);
    v_sz_8086_ = lean_array_size(v_params_8078_);
    v___x_8087_ = 0usize;
    v___x_8088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_8079_,
        v_params_8078_,
        v___f_8084_,
        v_sz_8086_,
        v___x_8087_,
        v___x_8085_,
    );
    v___x_8089_ = crate::leanh::lean_apply_4(
        v_toBind_8077_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_8088_,
        v___f_8080_,
    );
    return v___x_8089_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed(
    mut v_toPure_8090_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8091_: *mut crate::leanh::LeanObject,
    mut v___x_8092_: *mut crate::leanh::LeanObject,
    mut v_inst_8093_: *mut crate::leanh::LeanObject,
    mut v_toBind_8094_: *mut crate::leanh::LeanObject,
    mut v_params_8095_: *mut crate::leanh::LeanObject,
    mut v_inst_8096_: *mut crate::leanh::LeanObject,
    mut v___f_8097_: *mut crate::leanh::LeanObject,
    mut v_val_8098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_950__boxed_8099_: u8 = 0;
    let mut v_res_8100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_950__boxed_8099_ = (crate::leanh::lean_unbox(v___x_8092_) as u8);
    v_res_8100_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5(
        v_toPure_8090_,
        v_levels_x3f_8091_,
        v___x_950__boxed_8099_,
        v_inst_8093_,
        v_toBind_8094_,
        v_params_8095_,
        v_inst_8096_,
        v___f_8097_,
        v_val_8098_,
    );
    return v_res_8100_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(
    mut v_cinfo_8101_: *mut crate::leanh::LeanObject,
    mut v_us_8102_: *mut crate::leanh::LeanObject,
    mut v___x_8103_: u8,
    mut v___y_8104_: *mut crate::leanh::LeanObject,
    mut v___y_8105_: *mut crate::leanh::LeanObject,
    mut v___y_8106_: *mut crate::leanh::LeanObject,
    mut v___y_8107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8109_ = l_Lean_Core_instantiateValueLevelParams(
        v_cinfo_8101_,
        v_us_8102_,
        v___x_8103_,
        v___y_8106_,
        v___y_8107_,
    );
    return v___x_8109_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed(
    mut v_cinfo_8110_: *mut crate::leanh::LeanObject,
    mut v_us_8111_: *mut crate::leanh::LeanObject,
    mut v___x_8112_: *mut crate::leanh::LeanObject,
    mut v___y_8113_: *mut crate::leanh::LeanObject,
    mut v___y_8114_: *mut crate::leanh::LeanObject,
    mut v___y_8115_: *mut crate::leanh::LeanObject,
    mut v___y_8116_: *mut crate::leanh::LeanObject,
    mut v___y_8117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_976__boxed_8118_: u8 = 0;
    let mut v_res_8119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_976__boxed_8118_ = (crate::leanh::lean_unbox(v___x_8112_) as u8);
    v_res_8119_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6(
        v_cinfo_8110_,
        v_us_8111_,
        v___x_976__boxed_8118_,
        v___y_8113_,
        v___y_8114_,
        v___y_8115_,
        v___y_8116_,
    );
    crate::leanh::lean_dec(v___y_8116_);
    crate::leanh::lean_dec_ref(v___y_8115_);
    crate::leanh::lean_dec(v___y_8114_);
    crate::leanh::lean_dec_ref(v___y_8113_);
    crate::leanh::lean_dec_ref(v_cinfo_8110_);
    return v_res_8119_;
}
pub unsafe fn _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8123_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__2;
    v___x_8124_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_8125_ = crate::leanh::lean_unsigned_to_nat(202);
    v___x_8126_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__1;
    v___x_8127_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__0;
    v___x_8128_ = l_mkPanicMessageWithDecl(
        v___x_8127_,
        v___x_8126_,
        v___x_8125_,
        v___x_8124_,
        v___x_8123_,
    );
    return v___x_8128_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7(
    mut v_cinfo_8129_: *mut crate::leanh::LeanObject,
    mut v_inst_8130_: *mut crate::leanh::LeanObject,
    mut v_toPure_8131_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8132_: *mut crate::leanh::LeanObject,
    mut v_inst_8133_: *mut crate::leanh::LeanObject,
    mut v_toBind_8134_: *mut crate::leanh::LeanObject,
    mut v_params_8135_: *mut crate::leanh::LeanObject,
    mut v___f_8136_: *mut crate::leanh::LeanObject,
    mut v_us_8137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8141_: u8 = 0;
    v___x_8138_ = l_List_lengthTR___redArg(v_us_8137_);
    v___x_8139_ = l_Lean_ConstantInfo_levelParams(v_cinfo_8129_);
    v___x_8140_ = l_List_lengthTR___redArg(v___x_8139_);
    crate::leanh::lean_dec(v___x_8139_);
    v___x_8141_ = lean_nat_dec_eq(v___x_8138_, v___x_8140_);
    crate::leanh::lean_dec(v___x_8140_);
    crate::leanh::lean_dec(v___x_8138_);
    if v___x_8141_ == 0 {
        let mut v___x_8142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_us_8137_);
        crate::leanh::lean_dec(v___f_8136_);
        crate::leanh::lean_dec_ref(v_params_8135_);
        crate::leanh::lean_dec(v_toBind_8134_);
        crate::leanh::lean_dec(v_inst_8133_);
        crate::leanh::lean_dec(v_levels_x3f_8132_);
        crate::leanh::lean_dec(v_toPure_8131_);
        crate::leanh::lean_dec_ref(v_cinfo_8129_);
        v___x_8142_ = crate::leanh::lean_box(0);
        v___x_8143_ = l_instInhabitedOfMonad___redArg(v_inst_8130_, v___x_8142_);
        v___x_8144_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3_once
            ),
            _init_l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7___closed__3,
        );
        v___x_8145_ = l_panic___redArg(v___x_8143_, v___x_8144_);
        crate::leanh::lean_dec(v___x_8143_);
        return v___x_8145_;
    } else {
        let mut v___x_8146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8148_: u8 = 0;
        let mut v___x_8149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_8150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8146_ = crate::leanh::lean_box((v___x_8141_) as usize);
        crate::leanh::lean_inc(v_toBind_8134_);
        crate::leanh::lean_inc(v_inst_8133_);
        v___f_8147_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__5___boxed
                as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_8147_, 0, v_toPure_8131_);
        crate::leanh::lean_closure_set(v___f_8147_, 1, v_levels_x3f_8132_);
        crate::leanh::lean_closure_set(v___f_8147_, 2, v___x_8146_);
        crate::leanh::lean_closure_set(v___f_8147_, 3, v_inst_8133_);
        crate::leanh::lean_closure_set(v___f_8147_, 4, v_toBind_8134_);
        crate::leanh::lean_closure_set(v___f_8147_, 5, v_params_8135_);
        crate::leanh::lean_closure_set(v___f_8147_, 6, v_inst_8130_);
        crate::leanh::lean_closure_set(v___f_8147_, 7, v___f_8136_);
        v___x_8148_ = 0;
        v___x_8149_ = crate::leanh::lean_box((v___x_8148_) as usize);
        v___f_8150_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__6___boxed
                as *mut core::ffi::c_void,
            8,
            3,
        );
        crate::leanh::lean_closure_set(v___f_8150_, 0, v_cinfo_8129_);
        crate::leanh::lean_closure_set(v___f_8150_, 1, v_us_8137_);
        crate::leanh::lean_closure_set(v___f_8150_, 2, v___x_8149_);
        v___x_8151_ =
            crate::leanh::lean_apply_2(v_inst_8133_, crate::leanh::lean_box(0), v___f_8150_);
        v___x_8152_ = crate::leanh::lean_apply_4(
            v_toBind_8134_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_8151_,
            v___f_8147_,
        );
        return v___x_8152_;
    }
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8(
    mut v_inst_8153_: *mut crate::leanh::LeanObject,
    mut v_toPure_8154_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8155_: *mut crate::leanh::LeanObject,
    mut v_inst_8156_: *mut crate::leanh::LeanObject,
    mut v_toBind_8157_: *mut crate::leanh::LeanObject,
    mut v_params_8158_: *mut crate::leanh::LeanObject,
    mut v___f_8159_: *mut crate::leanh::LeanObject,
    mut v_cinfo_8160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_8161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_8157_);
    crate::leanh::lean_inc(v_inst_8156_);
    crate::leanh::lean_inc(v_levels_x3f_8155_);
    crate::leanh::lean_inc(v_toPure_8154_);
    crate::leanh::lean_inc_ref(v_cinfo_8160_);
    v___f_8161_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__7 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_8161_, 0, v_cinfo_8160_);
    crate::leanh::lean_closure_set(v___f_8161_, 1, v_inst_8153_);
    crate::leanh::lean_closure_set(v___f_8161_, 2, v_toPure_8154_);
    crate::leanh::lean_closure_set(v___f_8161_, 3, v_levels_x3f_8155_);
    crate::leanh::lean_closure_set(v___f_8161_, 4, v_inst_8156_);
    crate::leanh::lean_closure_set(v___f_8161_, 5, v_toBind_8157_);
    crate::leanh::lean_closure_set(v___f_8161_, 6, v_params_8158_);
    crate::leanh::lean_closure_set(v___f_8161_, 7, v___f_8159_);
    if crate::leanh::lean_obj_tag(v_levels_x3f_8155_) == 0 {
        let mut v___x_8162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_8154_);
        v___x_8162_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_mkFreshLevelMVarsFor___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        crate::leanh::lean_closure_set(v___x_8162_, 0, v_cinfo_8160_);
        v___x_8163_ =
            crate::leanh::lean_apply_2(v_inst_8156_, crate::leanh::lean_box(0), v___x_8162_);
        v___x_8164_ = crate::leanh::lean_apply_4(
            v_toBind_8157_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_8163_,
            v___f_8161_,
        );
        return v___x_8164_;
    } else {
        let mut v_val_8165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_cinfo_8160_);
        crate::leanh::lean_dec(v_inst_8156_);
        v_val_8165_ = crate::leanh::lean_ctor_get(v_levels_x3f_8155_, 0);
        crate::leanh::lean_inc(v_val_8165_);
        crate::leanh::lean_dec_ref_known(v_levels_x3f_8155_, 1);
        v___x_8166_ =
            crate::leanh::lean_apply_2(v_toPure_8154_, crate::leanh::lean_box(0), v_val_8165_);
        v___x_8167_ = crate::leanh::lean_apply_4(
            v_toBind_8157_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_8166_,
            v___f_8161_,
        );
        return v___x_8167_;
    }
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(
    mut v_inst_8168_: *mut crate::leanh::LeanObject,
    mut v_inst_8169_: *mut crate::leanh::LeanObject,
    mut v_inst_8170_: *mut crate::leanh::LeanObject,
    mut v_inst_8171_: *mut crate::leanh::LeanObject,
    mut v_defaultFn_8172_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8173_: *mut crate::leanh::LeanObject,
    mut v_params_8174_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_8175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_8176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_8177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_8178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_8176_ = crate::leanh::lean_ctor_get(v_inst_8168_, 0);
    v_toBind_8177_ = crate::leanh::lean_ctor_get(v_inst_8168_, 1);
    crate::leanh::lean_inc_n(v_toBind_8177_, 2);
    v_toPure_8178_ = crate::leanh::lean_ctor_get(v_toApplicative_8176_, 1);
    crate::leanh::lean_inc_n(v_toPure_8178_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_8168_, 2);
    v___x_8179_ =
        l_Lean_getConstInfo___redArg(v_inst_8168_, v_inst_8169_, v_inst_8170_, v_defaultFn_8172_);
    crate::leanh::lean_inc(v_inst_8171_);
    v___f_8180_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_8180_, 0, v_inst_8168_);
    crate::leanh::lean_closure_set(v___f_8180_, 1, v_inst_8171_);
    crate::leanh::lean_closure_set(v___f_8180_, 2, v_fieldVal_x3f_8175_);
    crate::leanh::lean_closure_set(v___f_8180_, 3, v_toPure_8178_);
    v___f_8181_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg___lam__8 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_8181_, 0, v_inst_8168_);
    crate::leanh::lean_closure_set(v___f_8181_, 1, v_toPure_8178_);
    crate::leanh::lean_closure_set(v___f_8181_, 2, v_levels_x3f_8173_);
    crate::leanh::lean_closure_set(v___f_8181_, 3, v_inst_8171_);
    crate::leanh::lean_closure_set(v___f_8181_, 4, v_toBind_8177_);
    crate::leanh::lean_closure_set(v___f_8181_, 5, v_params_8174_);
    crate::leanh::lean_closure_set(v___f_8181_, 6, v___f_8180_);
    v___x_8182_ = crate::leanh::lean_apply_4(
        v_toBind_8177_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_8179_,
        v___f_8181_,
    );
    return v___x_8182_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f(
    mut v_m_8183_: *mut crate::leanh::LeanObject,
    mut v_inst_8184_: *mut crate::leanh::LeanObject,
    mut v_inst_8185_: *mut crate::leanh::LeanObject,
    mut v_inst_8186_: *mut crate::leanh::LeanObject,
    mut v_inst_8187_: *mut crate::leanh::LeanObject,
    mut v_inst_8188_: *mut crate::leanh::LeanObject,
    mut v_defaultFn_8189_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8190_: *mut crate::leanh::LeanObject,
    mut v_params_8191_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_8192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8193_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f___redArg(
        v_inst_8184_,
        v_inst_8185_,
        v_inst_8186_,
        v_inst_8187_,
        v_defaultFn_8189_,
        v_levels_x3f_8190_,
        v_params_8191_,
        v_fieldVal_x3f_8192_,
    );
    return v___x_8193_;
}
pub unsafe fn l_Lean_Meta_instantiateStructDefaultValueFn_x3f___boxed(
    mut v_m_8194_: *mut crate::leanh::LeanObject,
    mut v_inst_8195_: *mut crate::leanh::LeanObject,
    mut v_inst_8196_: *mut crate::leanh::LeanObject,
    mut v_inst_8197_: *mut crate::leanh::LeanObject,
    mut v_inst_8198_: *mut crate::leanh::LeanObject,
    mut v_inst_8199_: *mut crate::leanh::LeanObject,
    mut v_defaultFn_8200_: *mut crate::leanh::LeanObject,
    mut v_levels_x3f_8201_: *mut crate::leanh::LeanObject,
    mut v_params_8202_: *mut crate::leanh::LeanObject,
    mut v_fieldVal_x3f_8203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8204_ = l_Lean_Meta_instantiateStructDefaultValueFn_x3f(
        v_m_8194_,
        v_inst_8195_,
        v_inst_8196_,
        v_inst_8197_,
        v_inst_8198_,
        v_inst_8199_,
        v_defaultFn_8200_,
        v_levels_x3f_8201_,
        v_params_8202_,
        v_fieldVal_x3f_8203_,
    );
    crate::leanh::lean_dec_ref(v_inst_8199_);
    return v_res_8204_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Structure(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Structure(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Structure(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Structure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Structure(builtin);
}
