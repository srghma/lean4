// Lean compiler output
// Module: Lean.Compiler.LCNF.InferType
// Imports: Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.OtherDecl Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_expr_abstract,
    lean_expr_abstract_range, lean_expr_eqv, lean_expr_instantiate_rev,
    lean_expr_instantiate_rev_range, lean_expr_instantiate1, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_monadNameGeneratorLift___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_ReaderT_instMonadLift___lam__0___boxed,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg,
    l_Lean_Compiler_LCNF_instInhabitedAlt_default__1,
    l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_getBinderName, l_Lean_Compiler_LCNF_getPhase___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg, l_Lean_Compiler_LCNF_getType,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg, l_Lean_Compiler_LCNF_mkFunDecl,
    l_Lean_Compiler_LCNF_mkLetDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::OtherDecl::{
    initialize_Lean_Compiler_LCNF_OtherDecl, l_Lean_Compiler_LCNF_getOtherDeclType,
    runtime_initialize_Lean_Compiler_LCNF_OtherDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_getDeclAt_x3f,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_anyExpr, l_Lean_Compiler_LCNF_erasedExpr,
    l_Lean_Compiler_LCNF_isPredicateType, l_Lean_Compiler_LCNF_joinTypes, l_Lean_Expr_isAny,
    l_Lean_Expr_isErased,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadNameGeneratorCoreM,
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
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_forallE___override,
    l_Lean_Expr_fvar___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_headBeta,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkFVar, l_Lean_mkFreshFVarId___redArg, l_Lean_mkProj,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_isEquiv, l_Lean_Level_normalize, l_Lean_Level_succ___override,
    l_Lean_mkLevelIMax_x27,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkLocalDecl, l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
    lean_local_ctx_find,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value:
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [108, 99, 69, 114, 97, 115, 101, 100, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__0_value)
            as *mut leanh::LeanObject,
        381462102099548843 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value:
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
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__3_value)
            as *mut leanh::LeanObject,
        3136308715950998022 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 73, 110, 116, 56, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__6_value)
            as *mut leanh::LeanObject,
        15764114953608429200 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value:
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
    m_data: [85, 73, 110, 116, 49, 54, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__9_value)
            as *mut leanh::LeanObject,
        9755723410228041222 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value:
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
    m_data: [85, 73, 110, 116, 51, 50, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13_value:
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
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__12_value
        ) as *mut leanh::LeanObject,
        13474504806189678690 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value:
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
    m_data: [85, 73, 110, 116, 54, 52, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16_value:
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
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__15_value
        ) as *mut leanh::LeanObject,
        2954612489107370298 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 83, 105, 122, 101, 0],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19_value:
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
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__18_value
        ) as *mut leanh::LeanObject,
        17712594561405737325 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73,
        110, 102, 101, 114, 84, 121, 112, 101, 46, 80, 117, 114, 101, 46, 105, 110, 102, 101, 114,
        84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73,
        110, 102, 101, 114, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_inferAppType___closed__0_value: leanh::LeanStringObject<32> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            105, 110, 102, 101, 114, 65, 112, 112, 84, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_inferAppType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inferAppType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_inferAppType___closed__1_value: leanh::LeanStringObject<36> =
    leanh::LeanStringObject {
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
            73, 110, 102, 101, 114, 32, 116, 121, 112, 101, 32, 102, 111, 114, 32, 105, 109, 112,
            117, 114, 101, 32, 117, 110, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_inferAppType___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inferAppType___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_inferAppType___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_inferAppType___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Arg_inferType___closed__0_value: leanh::LeanStringObject<
    33,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 65,
        114, 103, 46, 105, 110, 102, 101, 114, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Arg_inferType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Arg_inferType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Arg_inferType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_LetValue_inferType___closed__0_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 76,
        101, 116, 86, 97, 108, 117, 101, 46, 105, 110, 102, 101, 114, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_LetValue_inferType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_LetValue_inferType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_LetValue_inferType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Code_inferType___closed__0_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 67,
        111, 100, 101, 46, 105, 110, 102, 101, 114, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Code_inferType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Code_inferType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Code_inferType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Code_inferType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkForallParams___closed__0_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 109,
        107, 70, 111, 114, 97, 108, 108, 80, 97, 114, 97, 109, 115, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_mkForallParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkForallParams___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkForallParams___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkForallParams___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        96, 67, 111, 100, 101, 46, 98, 105, 110, 100, 96, 32, 102, 97, 105, 108, 101, 100, 44, 32,
        101, 109, 112, 116, 121, 32, 96, 99, 97, 115, 101, 115, 96, 32, 102, 111, 117, 110, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_mkCasesResultType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_mkCasesResultType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_mkCasesResultType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0_value: leanh::LeanStringObject<81> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 81, m_capacity: 81, m_length: 80, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 73, 110, 102, 101, 114, 84, 121, 112, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 105, 115, 69, 114, 97, 115, 101, 100, 67, 111, 109, 112, 97, 116, 105, 98, 108, 101, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(
    mut v_fvarId_2946_: *mut leanh::LeanObject,
    mut v_a_2947_: *mut leanh::LeanObject,
    mut v_a_2948_: *mut leanh::LeanObject,
    mut v_a_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_2946_);
                leanh::lean_inc_ref(v_a_2947_);
                v___x_2953_ = lean_local_ctx_find(v_a_2947_, v_fvarId_2946_);
                if leanh::lean_obj_tag(v___x_2953_) == 0 {
                    v___x_2954_ = l_Lean_Compiler_LCNF_getBinderName(
                        v_fvarId_2946_,
                        v_a_2948_,
                        v_a_2949_,
                        v_a_2950_,
                        v_a_2951_,
                    );
                    return v___x_2954_;
                } else {
                    leanh::lean_dec(v_fvarId_2946_);
                    v_val_2955_ = leanh::lean_ctor_get(v___x_2953_, 0);
                    v_isSharedCheck_2963_ = (!leanh::lean_is_exclusive(v___x_2953_)) as u8;
                    if v_isSharedCheck_2963_ == 0 {
                        v___x_2957_ = v___x_2953_;
                        v_isShared_2958_ = v_isSharedCheck_2963_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2955_);
                        leanh::lean_dec(v___x_2953_);
                        v___x_2957_ = leanh::lean_box(0);
                        v_isShared_2958_ = v_isSharedCheck_2963_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2959_ = l_Lean_LocalDecl_userName(v_val_2955_);
                leanh::lean_dec(v_val_2955_);
                if v_isShared_2958_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2957_, 0);
                    leanh::lean_ctor_set(v___x_2957_, 0, v___x_2959_);
                    v___x_2961_ = v___x_2957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
                    v___x_2961_ = v_reuseFailAlloc_2962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_getBinderName___boxed(
    mut v_fvarId_2964_: *mut leanh::LeanObject,
    mut v_a_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
    mut v_a_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(
        v_fvarId_2964_,
        v_a_2965_,
        v_a_2966_,
        v_a_2967_,
        v_a_2968_,
        v_a_2969_,
    );
    leanh::lean_dec(v_a_2969_);
    leanh::lean_dec_ref(v_a_2968_);
    leanh::lean_dec(v_a_2967_);
    leanh::lean_dec_ref(v_a_2966_);
    leanh::lean_dec_ref(v_a_2965_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_getType(
    mut v_fvarId_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
    mut v_a_2974_: *mut leanh::LeanObject,
    mut v_a_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_a_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2984_: u8 = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_fvarId_2972_);
                leanh::lean_inc_ref(v_a_2973_);
                v___x_2979_ = lean_local_ctx_find(v_a_2973_, v_fvarId_2972_);
                if leanh::lean_obj_tag(v___x_2979_) == 0 {
                    v___x_2980_ = l_Lean_Compiler_LCNF_getType(
                        v_fvarId_2972_,
                        v_a_2974_,
                        v_a_2975_,
                        v_a_2976_,
                        v_a_2977_,
                    );
                    return v___x_2980_;
                } else {
                    leanh::lean_dec(v_fvarId_2972_);
                    v_val_2981_ = leanh::lean_ctor_get(v___x_2979_, 0);
                    v_isSharedCheck_2989_ = (!leanh::lean_is_exclusive(v___x_2979_)) as u8;
                    if v_isSharedCheck_2989_ == 0 {
                        v___x_2983_ = v___x_2979_;
                        v_isShared_2984_ = v_isSharedCheck_2989_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2981_);
                        leanh::lean_dec(v___x_2979_);
                        v___x_2983_ = leanh::lean_box(0);
                        v_isShared_2984_ = v_isSharedCheck_2989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2985_ = l_Lean_LocalDecl_type(v_val_2981_);
                leanh::lean_dec(v_val_2981_);
                if v_isShared_2984_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2983_, 0);
                    leanh::lean_ctor_set(v___x_2983_, 0, v___x_2985_);
                    v___x_2987_ = v___x_2983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
                    v___x_2987_ = v_reuseFailAlloc_2988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_getType___boxed(
    mut v_fvarId_2990_: *mut leanh::LeanObject,
    mut v_a_2991_: *mut leanh::LeanObject,
    mut v_a_2992_: *mut leanh::LeanObject,
    mut v_a_2993_: *mut leanh::LeanObject,
    mut v_a_2994_: *mut leanh::LeanObject,
    mut v_a_2995_: *mut leanh::LeanObject,
    mut v_a_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(
        v_fvarId_2990_,
        v_a_2991_,
        v_a_2992_,
        v_a_2993_,
        v_a_2994_,
        v_a_2995_,
    );
    leanh::lean_dec(v_a_2995_);
    leanh::lean_dec_ref(v_a_2994_);
    leanh::lean_dec(v_a_2993_);
    leanh::lean_dec_ref(v_a_2992_);
    leanh::lean_dec_ref(v_a_2991_);
    return v_res_2997_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(
    mut v_xs_2998_: *mut leanh::LeanObject,
    mut v_i_2999_: *mut leanh::LeanObject,
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v___y_3001_: *mut leanh::LeanObject,
    mut v___y_3002_: *mut leanh::LeanObject,
    mut v___y_3003_: *mut leanh::LeanObject,
    mut v___y_3004_: *mut leanh::LeanObject,
    mut v___y_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3008_: u8 = 0;
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3007_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3008_ = lean_nat_dec_eq(v_i_2999_, v_zero_3007_);
                if v_isZero_3008_ == 1 {
                    leanh::lean_dec(v_i_2999_);
                    v___x_3009_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3009_, 0, v_a_3000_);
                    return v___x_3009_;
                } else {
                    v_one_3010_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3011_ = lean_nat_sub(v_i_2999_, v_one_3010_);
                    leanh::lean_dec(v_i_2999_);
                    v_x_3012_ = lean_array_fget_borrowed(v_xs_2998_, v_n_3011_);
                    v___x_3013_ = l_Lean_Expr_fvarId_x21(v_x_3012_);
                    leanh::lean_inc(v___x_3013_);
                    v___x_3014_ = l_Lean_Compiler_LCNF_InferType_Pure_getBinderName(
                        v___x_3013_,
                        v___y_3001_,
                        v___y_3002_,
                        v___y_3003_,
                        v___y_3004_,
                        v___y_3005_,
                    );
                    if leanh::lean_obj_tag(v___x_3014_) == 0 {
                        v_a_3015_ = leanh::lean_ctor_get(v___x_3014_, 0);
                        leanh::lean_inc(v_a_3015_);
                        leanh::lean_dec_ref_known(v___x_3014_, 1);
                        v___x_3016_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(
                            v___x_3013_,
                            v___y_3001_,
                            v___y_3002_,
                            v___y_3003_,
                            v___y_3004_,
                            v___y_3005_,
                        );
                        if leanh::lean_obj_tag(v___x_3016_) == 0 {
                            v_a_3017_ = leanh::lean_ctor_get(v___x_3016_, 0);
                            leanh::lean_inc(v_a_3017_);
                            leanh::lean_dec_ref_known(v___x_3016_, 1);
                            v___x_3018_ =
                                lean_expr_abstract_range(v_a_3017_, v_n_3011_, v_xs_2998_);
                            leanh::lean_dec(v_a_3017_);
                            v___x_3019_ = 0;
                            v___x_3020_ = l_Lean_Expr_forallE___override(
                                v_a_3015_,
                                v___x_3018_,
                                v_a_3000_,
                                v___x_3019_,
                            );
                            v_i_2999_ = v_n_3011_;
                            v_a_3000_ = v___x_3020_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3015_);
                            leanh::lean_dec_ref(v_a_3000_);
                            if leanh::lean_obj_tag(v___x_3016_) == 0 {
                                v_a_3022_ = leanh::lean_ctor_get(v___x_3016_, 0);
                                leanh::lean_inc(v_a_3022_);
                                leanh::lean_dec_ref_known(v___x_3016_, 1);
                                v_i_2999_ = v_n_3011_;
                                v_a_3000_ = v_a_3022_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v_n_3011_);
                                return v___x_3016_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_3013_);
                        leanh::lean_dec(v_n_3011_);
                        leanh::lean_dec_ref(v_a_3000_);
                        v_a_3024_ = leanh::lean_ctor_get(v___x_3014_, 0);
                        v_isSharedCheck_3031_ =
                            (!leanh::lean_is_exclusive(v___x_3014_)) as u8;
                        if v_isSharedCheck_3031_ == 0 {
                            v___x_3026_ = v___x_3014_;
                            v_isShared_3027_ = v_isSharedCheck_3031_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3024_);
                            leanh::lean_dec(v___x_3014_);
                            v___x_3026_ = leanh::lean_box(0);
                            v_isShared_3027_ = v_isSharedCheck_3031_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3027_ == 0 {
                    v___x_3029_ = v___x_3026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg___boxed(
    mut v_xs_3032_: *mut leanh::LeanObject,
    mut v_i_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
    mut v___y_3035_: *mut leanh::LeanObject,
    mut v___y_3036_: *mut leanh::LeanObject,
    mut v___y_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
    mut v___y_3039_: *mut leanh::LeanObject,
    mut v___y_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3041_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_3032_, v_i_3033_, v_a_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
    leanh::lean_dec(v___y_3039_);
    leanh::lean_dec_ref(v___y_3038_);
    leanh::lean_dec(v___y_3037_);
    leanh::lean_dec_ref(v___y_3036_);
    leanh::lean_dec_ref(v___y_3035_);
    leanh::lean_dec_ref(v_xs_3032_);
    return v_res_3041_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(
    mut v_xs_3042_: *mut leanh::LeanObject,
    mut v_type_3043_: *mut leanh::LeanObject,
    mut v_a_3044_: *mut leanh::LeanObject,
    mut v_a_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
    mut v_a_3048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_3050_ = lean_expr_abstract(v_type_3043_, v_xs_3042_);
    v___x_3051_ = lean_array_get_size(v_xs_3042_);
    v___x_3052_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_3042_, v___x_3051_, v_b_3050_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
    return v___x_3052_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars___boxed(
    mut v_xs_3053_: *mut leanh::LeanObject,
    mut v_type_3054_: *mut leanh::LeanObject,
    mut v_a_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
    mut v_a_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
    mut v_a_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(
        v_xs_3053_,
        v_type_3054_,
        v_a_3055_,
        v_a_3056_,
        v_a_3057_,
        v_a_3058_,
        v_a_3059_,
    );
    leanh::lean_dec(v_a_3059_);
    leanh::lean_dec_ref(v_a_3058_);
    leanh::lean_dec(v_a_3057_);
    leanh::lean_dec_ref(v_a_3056_);
    leanh::lean_dec_ref(v_a_3055_);
    leanh::lean_dec_ref(v_type_3054_);
    leanh::lean_dec_ref(v_xs_3053_);
    return v_res_3061_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(
    mut v_xs_3062_: *mut leanh::LeanObject,
    mut v_n_3063_: *mut leanh::LeanObject,
    mut v_i_3064_: *mut leanh::LeanObject,
    mut v_a_3065_: *mut leanh::LeanObject,
    mut v_a_3066_: *mut leanh::LeanObject,
    mut v___y_3067_: *mut leanh::LeanObject,
    mut v___y_3068_: *mut leanh::LeanObject,
    mut v___y_3069_: *mut leanh::LeanObject,
    mut v___y_3070_: *mut leanh::LeanObject,
    mut v___y_3071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3073_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___redArg(v_xs_3062_, v_i_3064_, v_a_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
    return v___x_3073_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0___boxed(
    mut v_xs_3074_: *mut leanh::LeanObject,
    mut v_n_3075_: *mut leanh::LeanObject,
    mut v_i_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
    mut v___y_3079_: *mut leanh::LeanObject,
    mut v___y_3080_: *mut leanh::LeanObject,
    mut v___y_3081_: *mut leanh::LeanObject,
    mut v___y_3082_: *mut leanh::LeanObject,
    mut v___y_3083_: *mut leanh::LeanObject,
    mut v___y_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3085_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallFVars_spec__0(v_xs_3074_, v_n_3075_, v_i_3076_, v_a_3077_, v_a_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
    leanh::lean_dec(v___y_3083_);
    leanh::lean_dec_ref(v___y_3082_);
    leanh::lean_dec(v___y_3081_);
    leanh::lean_dec_ref(v___y_3080_);
    leanh::lean_dec_ref(v___y_3079_);
    leanh::lean_dec(v_n_3075_);
    leanh::lean_dec_ref(v_xs_3074_);
    return v_res_3085_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(
    mut v_sz_3086_: usize,
    mut v_i_3087_: usize,
    mut v_bs_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3089_: u8 = 0;
    let mut v_v_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: usize = 0;
    let mut v___x_3096_: usize = 0;
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3089_ = lean_usize_dec_lt(v_i_3087_, v_sz_3086_);
                if v___x_3089_ == 0 {
                    return v_bs_3088_;
                } else {
                    v_v_3090_ = lean_array_uget_borrowed(v_bs_3088_, v_i_3087_);
                    v_fvarId_3091_ = leanh::lean_ctor_get(v_v_3090_, 0);
                    leanh::lean_inc(v_fvarId_3091_);
                    v___x_3092_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3093_ = lean_array_uset(v_bs_3088_, v_i_3087_, v___x_3092_);
                    v___x_3094_ = l_Lean_Expr_fvar___override(v_fvarId_3091_);
                    v___x_3095_ = 1usize;
                    v___x_3096_ = lean_usize_add(v_i_3087_, v___x_3095_);
                    v___x_3097_ = lean_array_uset(v_bs_x27_3093_, v_i_3087_, v___x_3094_);
                    v_i_3087_ = v___x_3096_;
                    v_bs_3088_ = v___x_3097_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0___boxed(
    mut v_sz_3099_: *mut leanh::LeanObject,
    mut v_i_3100_: *mut leanh::LeanObject,
    mut v_bs_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3102_: usize = 0;
    let mut v_i_boxed_3103_: usize = 0;
    let mut v_res_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3102_ = leanh::lean_unbox_usize(v_sz_3099_);
    leanh::lean_dec(v_sz_3099_);
    v_i_boxed_3103_ = leanh::lean_unbox_usize(v_i_3100_);
    leanh::lean_dec(v_i_3100_);
    v_res_3104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_boxed_3102_, v_i_boxed_3103_, v_bs_3101_);
    return v_res_3104_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__0,
    );
    v___x_3107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3107_, 0, v___x_3106_);
    return v___x_3107_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = leanh::lean_unsigned_to_nat(32);
    v___x_3109_ = lean_mk_empty_array_with_capacity(v___x_3108_);
    v___x_3110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
    return v___x_3110_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3111_ = 5usize;
    v___x_3112_ = leanh::lean_unsigned_to_nat(0);
    v___x_3113_ = leanh::lean_unsigned_to_nat(32);
    v___x_3114_ = lean_mk_empty_array_with_capacity(v___x_3113_);
    v___x_3115_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__2,
    );
    v___x_3116_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3116_, 0, v___x_3115_);
    leanh::lean_ctor_set(v___x_3116_, 1, v___x_3114_);
    leanh::lean_ctor_set(v___x_3116_, 2, v___x_3112_);
    leanh::lean_ctor_set(v___x_3116_, 3, v___x_3112_);
    leanh::lean_ctor_set_usize(v___x_3116_, 4, v___x_3111_);
    return v___x_3116_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3117_ = leanh::lean_box(1);
    v___x_3118_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3,
    );
    v___x_3119_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__1,
    );
    v___x_3120_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3120_, 0, v___x_3119_);
    leanh::lean_ctor_set(v___x_3120_, 1, v___x_3118_);
    leanh::lean_ctor_set(v___x_3120_, 2, v___x_3117_);
    return v___x_3120_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(
    mut v_params_3121_: *mut leanh::LeanObject,
    mut v_type_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
    mut v_a_3125_: *mut leanh::LeanObject,
    mut v_a_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_3128_: usize = 0;
    let mut v___x_3129_: usize = 0;
    let mut v_xs_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_3128_ = lean_array_size(v_params_3121_);
    v___x_3129_ = 0usize;
    v_xs_3130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_3128_, v___x_3129_, v_params_3121_);
    v___x_3131_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4,
    );
    v___x_3132_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(
        v_xs_3130_,
        v_type_3122_,
        v___x_3131_,
        v_a_3123_,
        v_a_3124_,
        v_a_3125_,
        v_a_3126_,
    );
    leanh::lean_dec_ref(v_xs_3130_);
    return v___x_3132_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___boxed(
    mut v_params_3133_: *mut leanh::LeanObject,
    mut v_type_3134_: *mut leanh::LeanObject,
    mut v_a_3135_: *mut leanh::LeanObject,
    mut v_a_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3140_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(
        v_params_3133_,
        v_type_3134_,
        v_a_3135_,
        v_a_3136_,
        v_a_3137_,
        v_a_3138_,
    );
    leanh::lean_dec(v_a_3138_);
    leanh::lean_dec_ref(v_a_3137_);
    leanh::lean_dec(v_a_3136_);
    leanh::lean_dec_ref(v_a_3135_);
    leanh::lean_dec_ref(v_type_3134_);
    return v_res_3140_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(
    mut v_params_3141_: *mut leanh::LeanObject,
    mut v_type_3142_: *mut leanh::LeanObject,
    mut v_a_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3149_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(
        v_params_3141_,
        v_type_3142_,
        v_a_3144_,
        v_a_3145_,
        v_a_3146_,
        v_a_3147_,
    );
    return v___x_3149_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___boxed(
    mut v_params_3150_: *mut leanh::LeanObject,
    mut v_type_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
    mut v_a_3155_: *mut leanh::LeanObject,
    mut v_a_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams(
        v_params_3150_,
        v_type_3151_,
        v_a_3152_,
        v_a_3153_,
        v_a_3154_,
        v_a_3155_,
        v_a_3156_,
    );
    leanh::lean_dec(v_a_3156_);
    leanh::lean_dec_ref(v_a_3155_);
    leanh::lean_dec(v_a_3154_);
    leanh::lean_dec_ref(v_a_3153_);
    leanh::lean_dec_ref(v_a_3152_);
    leanh::lean_dec_ref(v_type_3151_);
    return v_res_3158_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3159_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_3159_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3160_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__0,
    );
    v___x_3161_ = l_StateRefT_x27_instMonad___redArg(v___x_3160_);
    return v___x_3161_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lean_Core_instMonadNameGeneratorCoreM;
    v___x_3169_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__7;
    v___x_3170_ = l_Lean_monadNameGeneratorLift___redArg(v___x_3169_, v___x_3168_);
    return v___x_3170_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3171_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__8,
    );
    v___f_3172_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6;
    v___x_3173_ = l_Lean_monadNameGeneratorLift___redArg(v___f_3172_, v___x_3171_);
    return v___x_3173_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3174_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__9,
    );
    v___f_3175_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__6;
    v___x_3176_ = l_Lean_monadNameGeneratorLift___redArg(v___f_3175_, v___x_3174_);
    return v___x_3176_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(
    mut v_binderName_3177_: *mut leanh::LeanObject,
    mut v_type_3178_: *mut leanh::LeanObject,
    mut v_binderInfo_3179_: u8,
    mut v_k_3180_: *mut leanh::LeanObject,
    mut v_a_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
    mut v_a_3183_: *mut leanh::LeanObject,
    mut v_a_3184_: *mut leanh::LeanObject,
    mut v_a_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v_toFunctor_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___f_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157__overap_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3243_: u8 = 0;
    let mut v_reuseFailAlloc_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut v_unused_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_unused_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3187_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1,
                );
                v_toApplicative_3188_ = leanh::lean_ctor_get(v___x_3187_, 0);
                v_toFunctor_3189_ = leanh::lean_ctor_get(v_toApplicative_3188_, 0);
                v_toSeq_3190_ = leanh::lean_ctor_get(v_toApplicative_3188_, 2);
                v_toSeqLeft_3191_ = leanh::lean_ctor_get(v_toApplicative_3188_, 3);
                v_toSeqRight_3192_ = leanh::lean_ctor_get(v_toApplicative_3188_, 4);
                v___f_3193_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2;
                v___f_3194_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_3189_, 2);
                v___f_3195_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3195_, 0, v_toFunctor_3189_);
                v___f_3196_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3196_, 0, v_toFunctor_3189_);
                v___x_3197_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3197_, 0, v___f_3195_);
                leanh::lean_ctor_set(v___x_3197_, 1, v___f_3196_);
                leanh::lean_inc(v_toSeqRight_3192_);
                v___f_3198_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3198_, 0, v_toSeqRight_3192_);
                leanh::lean_inc(v_toSeqLeft_3191_);
                v___f_3199_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3199_, 0, v_toSeqLeft_3191_);
                leanh::lean_inc(v_toSeq_3190_);
                v___f_3200_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3200_, 0, v_toSeq_3190_);
                v___x_3201_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3201_, 0, v___x_3197_);
                leanh::lean_ctor_set(v___x_3201_, 1, v___f_3193_);
                leanh::lean_ctor_set(v___x_3201_, 2, v___f_3200_);
                leanh::lean_ctor_set(v___x_3201_, 3, v___f_3199_);
                leanh::lean_ctor_set(v___x_3201_, 4, v___f_3198_);
                v___x_3202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3202_, 0, v___x_3201_);
                leanh::lean_ctor_set(v___x_3202_, 1, v___f_3194_);
                v___x_3203_ = l_StateRefT_x27_instMonad___redArg(v___x_3202_);
                v_toApplicative_3204_ = leanh::lean_ctor_get(v___x_3203_, 0);
                v_isSharedCheck_3248_ = (!leanh::lean_is_exclusive(v___x_3203_)) as u8;
                if v_isSharedCheck_3248_ == 0 {
                    v_unused_3249_ = leanh::lean_ctor_get(v___x_3203_, 1);
                    leanh::lean_dec(v_unused_3249_);
                    v___x_3206_ = v___x_3203_;
                    v_isShared_3207_ = v_isSharedCheck_3248_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3204_);
                    leanh::lean_dec(v___x_3203_);
                    v___x_3206_ = leanh::lean_box(0);
                    v_isShared_3207_ = v_isSharedCheck_3248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3208_ = leanh::lean_ctor_get(v_toApplicative_3204_, 0);
                v_toSeq_3209_ = leanh::lean_ctor_get(v_toApplicative_3204_, 2);
                v_toSeqLeft_3210_ = leanh::lean_ctor_get(v_toApplicative_3204_, 3);
                v_toSeqRight_3211_ = leanh::lean_ctor_get(v_toApplicative_3204_, 4);
                v_isSharedCheck_3246_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3204_)) as u8;
                if v_isSharedCheck_3246_ == 0 {
                    v_unused_3247_ = leanh::lean_ctor_get(v_toApplicative_3204_, 1);
                    leanh::lean_dec(v_unused_3247_);
                    v___x_3213_ = v_toApplicative_3204_;
                    v_isShared_3214_ = v_isSharedCheck_3246_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3211_);
                    leanh::lean_inc(v_toSeqLeft_3210_);
                    leanh::lean_inc(v_toSeq_3209_);
                    leanh::lean_inc(v_toFunctor_3208_);
                    leanh::lean_dec(v_toApplicative_3204_);
                    v___x_3213_ = leanh::lean_box(0);
                    v_isShared_3214_ = v_isSharedCheck_3246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3215_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4;
                v___f_3216_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_3208_);
                v___f_3217_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3217_, 0, v_toFunctor_3208_);
                v___f_3218_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3218_, 0, v_toFunctor_3208_);
                v___x_3219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3219_, 0, v___f_3217_);
                leanh::lean_ctor_set(v___x_3219_, 1, v___f_3218_);
                v___f_3220_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3220_, 0, v_toSeqRight_3211_);
                v___f_3221_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3221_, 0, v_toSeqLeft_3210_);
                v___f_3222_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3222_, 0, v_toSeq_3209_);
                if v_isShared_3214_ == 0 {
                    leanh::lean_ctor_set(v___x_3213_, 4, v___f_3220_);
                    leanh::lean_ctor_set(v___x_3213_, 3, v___f_3221_);
                    leanh::lean_ctor_set(v___x_3213_, 2, v___f_3222_);
                    leanh::lean_ctor_set(v___x_3213_, 1, v___f_3215_);
                    leanh::lean_ctor_set(v___x_3213_, 0, v___x_3219_);
                    v___x_3224_ = v___x_3213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3245_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 1, v___f_3215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 2, v___f_3222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 3, v___f_3221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 4, v___f_3220_);
                    v___x_3224_ = v_reuseFailAlloc_3245_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3207_ == 0 {
                    leanh::lean_ctor_set(v___x_3206_, 1, v___f_3216_);
                    leanh::lean_ctor_set(v___x_3206_, 0, v___x_3224_);
                    v___x_3226_ = v___x_3206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3244_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 1, v___f_3216_);
                    v___x_3226_ = v_reuseFailAlloc_3244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3227_ = l_ReaderT_instMonad___redArg(v___x_3226_);
                v___x_3228_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once), _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
                v___x_157__overap_3229_ = l_Lean_mkFreshFVarId___redArg(v___x_3227_, v___x_3228_);
                leanh::lean_inc(v_a_3185_);
                leanh::lean_inc_ref(v_a_3184_);
                leanh::lean_inc(v_a_3183_);
                leanh::lean_inc_ref(v_a_3182_);
                leanh::lean_inc_ref(v_a_3181_);
                v___x_3230_ = leanh::lean_apply_6(
                    v___x_157__overap_3229_,
                    v_a_3181_,
                    v_a_3182_,
                    v_a_3183_,
                    v_a_3184_,
                    v_a_3185_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3230_) == 0 {
                    v_a_3231_ = leanh::lean_ctor_get(v___x_3230_, 0);
                    leanh::lean_inc_n(v_a_3231_, 2);
                    leanh::lean_dec_ref_known(v___x_3230_, 1);
                    v___x_3232_ = l_Lean_Expr_fvar___override(v_a_3231_);
                    v___x_3233_ = 0;
                    leanh::lean_inc_ref(v_a_3181_);
                    v___x_3234_ = l_Lean_LocalContext_mkLocalDecl(
                        v_a_3181_,
                        v_a_3231_,
                        v_binderName_3177_,
                        v_type_3178_,
                        v_binderInfo_3179_,
                        v___x_3233_,
                    );
                    leanh::lean_inc(v_a_3185_);
                    leanh::lean_inc_ref(v_a_3184_);
                    leanh::lean_inc(v_a_3183_);
                    leanh::lean_inc_ref(v_a_3182_);
                    v___x_3235_ = leanh::lean_apply_7(
                        v_k_3180_,
                        v___x_3232_,
                        v___x_3234_,
                        v_a_3182_,
                        v_a_3183_,
                        v_a_3184_,
                        v_a_3185_,
                        leanh::lean_box(0),
                    );
                    return v___x_3235_;
                } else {
                    leanh::lean_dec_ref(v_k_3180_);
                    leanh::lean_dec_ref(v_type_3178_);
                    leanh::lean_dec(v_binderName_3177_);
                    v_a_3236_ = leanh::lean_ctor_get(v___x_3230_, 0);
                    v_isSharedCheck_3243_ = (!leanh::lean_is_exclusive(v___x_3230_)) as u8;
                    if v_isSharedCheck_3243_ == 0 {
                        v___x_3238_ = v___x_3230_;
                        v_isShared_3239_ = v_isSharedCheck_3243_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3236_);
                        leanh::lean_dec(v___x_3230_);
                        v___x_3238_ = leanh::lean_box(0);
                        v_isShared_3239_ = v_isSharedCheck_3243_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3239_ == 0 {
                    v___x_3241_ = v___x_3238_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
                    v___x_3241_ = v_reuseFailAlloc_3242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___boxed(
    mut v_binderName_3250_: *mut leanh::LeanObject,
    mut v_type_3251_: *mut leanh::LeanObject,
    mut v_binderInfo_3252_: *mut leanh::LeanObject,
    mut v_k_3253_: *mut leanh::LeanObject,
    mut v_a_3254_: *mut leanh::LeanObject,
    mut v_a_3255_: *mut leanh::LeanObject,
    mut v_a_3256_: *mut leanh::LeanObject,
    mut v_a_3257_: *mut leanh::LeanObject,
    mut v_a_3258_: *mut leanh::LeanObject,
    mut v_a_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_boxed_3260_: u8 = 0;
    let mut v_res_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_boxed_3260_ = (leanh::lean_unbox(v_binderInfo_3252_) as u8);
    v_res_3261_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg(
        v_binderName_3250_,
        v_type_3251_,
        v_binderInfo_boxed_3260_,
        v_k_3253_,
        v_a_3254_,
        v_a_3255_,
        v_a_3256_,
        v_a_3257_,
        v_a_3258_,
    );
    leanh::lean_dec(v_a_3258_);
    leanh::lean_dec_ref(v_a_3257_);
    leanh::lean_dec(v_a_3256_);
    leanh::lean_dec_ref(v_a_3255_);
    leanh::lean_dec_ref(v_a_3254_);
    return v_res_3261_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(
    mut v_00_u03b1_3262_: *mut leanh::LeanObject,
    mut v_binderName_3263_: *mut leanh::LeanObject,
    mut v_type_3264_: *mut leanh::LeanObject,
    mut v_binderInfo_3265_: u8,
    mut v_k_3266_: *mut leanh::LeanObject,
    mut v_a_3267_: *mut leanh::LeanObject,
    mut v_a_3268_: *mut leanh::LeanObject,
    mut v_a_3269_: *mut leanh::LeanObject,
    mut v_a_3270_: *mut leanh::LeanObject,
    mut v_a_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3293_: u8 = 0;
    let mut v_toFunctor_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v___f_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226__overap_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u8 = 0;
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3329_: u8 = 0;
    let mut v_reuseFailAlloc_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v_unused_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut v_unused_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3273_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1,
                );
                v_toApplicative_3274_ = leanh::lean_ctor_get(v___x_3273_, 0);
                v_toFunctor_3275_ = leanh::lean_ctor_get(v_toApplicative_3274_, 0);
                v_toSeq_3276_ = leanh::lean_ctor_get(v_toApplicative_3274_, 2);
                v_toSeqLeft_3277_ = leanh::lean_ctor_get(v_toApplicative_3274_, 3);
                v_toSeqRight_3278_ = leanh::lean_ctor_get(v_toApplicative_3274_, 4);
                v___f_3279_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2;
                v___f_3280_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_3275_, 2);
                v___f_3281_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3281_, 0, v_toFunctor_3275_);
                v___f_3282_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3282_, 0, v_toFunctor_3275_);
                v___x_3283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3283_, 0, v___f_3281_);
                leanh::lean_ctor_set(v___x_3283_, 1, v___f_3282_);
                leanh::lean_inc(v_toSeqRight_3278_);
                v___f_3284_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3284_, 0, v_toSeqRight_3278_);
                leanh::lean_inc(v_toSeqLeft_3277_);
                v___f_3285_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3285_, 0, v_toSeqLeft_3277_);
                leanh::lean_inc(v_toSeq_3276_);
                v___f_3286_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3286_, 0, v_toSeq_3276_);
                v___x_3287_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3287_, 0, v___x_3283_);
                leanh::lean_ctor_set(v___x_3287_, 1, v___f_3279_);
                leanh::lean_ctor_set(v___x_3287_, 2, v___f_3286_);
                leanh::lean_ctor_set(v___x_3287_, 3, v___f_3285_);
                leanh::lean_ctor_set(v___x_3287_, 4, v___f_3284_);
                v___x_3288_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3288_, 0, v___x_3287_);
                leanh::lean_ctor_set(v___x_3288_, 1, v___f_3280_);
                v___x_3289_ = l_StateRefT_x27_instMonad___redArg(v___x_3288_);
                v_toApplicative_3290_ = leanh::lean_ctor_get(v___x_3289_, 0);
                v_isSharedCheck_3334_ = (!leanh::lean_is_exclusive(v___x_3289_)) as u8;
                if v_isSharedCheck_3334_ == 0 {
                    v_unused_3335_ = leanh::lean_ctor_get(v___x_3289_, 1);
                    leanh::lean_dec(v_unused_3335_);
                    v___x_3292_ = v___x_3289_;
                    v_isShared_3293_ = v_isSharedCheck_3334_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3290_);
                    leanh::lean_dec(v___x_3289_);
                    v___x_3292_ = leanh::lean_box(0);
                    v_isShared_3293_ = v_isSharedCheck_3334_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3294_ = leanh::lean_ctor_get(v_toApplicative_3290_, 0);
                v_toSeq_3295_ = leanh::lean_ctor_get(v_toApplicative_3290_, 2);
                v_toSeqLeft_3296_ = leanh::lean_ctor_get(v_toApplicative_3290_, 3);
                v_toSeqRight_3297_ = leanh::lean_ctor_get(v_toApplicative_3290_, 4);
                v_isSharedCheck_3332_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3290_)) as u8;
                if v_isSharedCheck_3332_ == 0 {
                    v_unused_3333_ = leanh::lean_ctor_get(v_toApplicative_3290_, 1);
                    leanh::lean_dec(v_unused_3333_);
                    v___x_3299_ = v_toApplicative_3290_;
                    v_isShared_3300_ = v_isSharedCheck_3332_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3297_);
                    leanh::lean_inc(v_toSeqLeft_3296_);
                    leanh::lean_inc(v_toSeq_3295_);
                    leanh::lean_inc(v_toFunctor_3294_);
                    leanh::lean_dec(v_toApplicative_3290_);
                    v___x_3299_ = leanh::lean_box(0);
                    v_isShared_3300_ = v_isSharedCheck_3332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3301_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__4;
                v___f_3302_ =
                    l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_3294_);
                v___f_3303_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3303_, 0, v_toFunctor_3294_);
                v___f_3304_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3304_, 0, v_toFunctor_3294_);
                v___x_3305_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3305_, 0, v___f_3303_);
                leanh::lean_ctor_set(v___x_3305_, 1, v___f_3304_);
                v___f_3306_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3306_, 0, v_toSeqRight_3297_);
                v___f_3307_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3307_, 0, v_toSeqLeft_3296_);
                v___f_3308_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3308_, 0, v_toSeq_3295_);
                if v_isShared_3300_ == 0 {
                    leanh::lean_ctor_set(v___x_3299_, 4, v___f_3306_);
                    leanh::lean_ctor_set(v___x_3299_, 3, v___f_3307_);
                    leanh::lean_ctor_set(v___x_3299_, 2, v___f_3308_);
                    leanh::lean_ctor_set(v___x_3299_, 1, v___f_3301_);
                    leanh::lean_ctor_set(v___x_3299_, 0, v___x_3305_);
                    v___x_3310_ = v___x_3299_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 1, v___f_3301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 2, v___f_3308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 3, v___f_3307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 4, v___f_3306_);
                    v___x_3310_ = v_reuseFailAlloc_3331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3293_ == 0 {
                    leanh::lean_ctor_set(v___x_3292_, 1, v___f_3302_);
                    leanh::lean_ctor_set(v___x_3292_, 0, v___x_3310_);
                    v___x_3312_ = v___x_3292_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___f_3302_);
                    v___x_3312_ = v_reuseFailAlloc_3330_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3313_ = l_ReaderT_instMonad___redArg(v___x_3312_);
                v___x_3314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10_once), _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__10);
                v___x_226__overap_3315_ = l_Lean_mkFreshFVarId___redArg(v___x_3313_, v___x_3314_);
                leanh::lean_inc(v_a_3271_);
                leanh::lean_inc_ref(v_a_3270_);
                leanh::lean_inc(v_a_3269_);
                leanh::lean_inc_ref(v_a_3268_);
                leanh::lean_inc_ref(v_a_3267_);
                v___x_3316_ = leanh::lean_apply_6(
                    v___x_226__overap_3315_,
                    v_a_3267_,
                    v_a_3268_,
                    v_a_3269_,
                    v_a_3270_,
                    v_a_3271_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3316_) == 0 {
                    v_a_3317_ = leanh::lean_ctor_get(v___x_3316_, 0);
                    leanh::lean_inc_n(v_a_3317_, 2);
                    leanh::lean_dec_ref_known(v___x_3316_, 1);
                    v___x_3318_ = l_Lean_Expr_fvar___override(v_a_3317_);
                    v___x_3319_ = 0;
                    leanh::lean_inc_ref(v_a_3267_);
                    v___x_3320_ = l_Lean_LocalContext_mkLocalDecl(
                        v_a_3267_,
                        v_a_3317_,
                        v_binderName_3263_,
                        v_type_3264_,
                        v_binderInfo_3265_,
                        v___x_3319_,
                    );
                    leanh::lean_inc(v_a_3271_);
                    leanh::lean_inc_ref(v_a_3270_);
                    leanh::lean_inc(v_a_3269_);
                    leanh::lean_inc_ref(v_a_3268_);
                    v___x_3321_ = leanh::lean_apply_7(
                        v_k_3266_,
                        v___x_3318_,
                        v___x_3320_,
                        v_a_3268_,
                        v_a_3269_,
                        v_a_3270_,
                        v_a_3271_,
                        leanh::lean_box(0),
                    );
                    return v___x_3321_;
                } else {
                    leanh::lean_dec_ref(v_k_3266_);
                    leanh::lean_dec_ref(v_type_3264_);
                    leanh::lean_dec(v_binderName_3263_);
                    v_a_3322_ = leanh::lean_ctor_get(v___x_3316_, 0);
                    v_isSharedCheck_3329_ = (!leanh::lean_is_exclusive(v___x_3316_)) as u8;
                    if v_isSharedCheck_3329_ == 0 {
                        v___x_3324_ = v___x_3316_;
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3322_);
                        leanh::lean_dec(v___x_3316_);
                        v___x_3324_ = leanh::lean_box(0);
                        v_isShared_3325_ = v_isSharedCheck_3329_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3325_ == 0 {
                    v___x_3327_ = v___x_3324_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
                    v___x_3327_ = v_reuseFailAlloc_3328_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___boxed(
    mut v_00_u03b1_3336_: *mut leanh::LeanObject,
    mut v_binderName_3337_: *mut leanh::LeanObject,
    mut v_type_3338_: *mut leanh::LeanObject,
    mut v_binderInfo_3339_: *mut leanh::LeanObject,
    mut v_k_3340_: *mut leanh::LeanObject,
    mut v_a_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderInfo_boxed_3347_: u8 = 0;
    let mut v_res_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_boxed_3347_ = (leanh::lean_unbox(v_binderInfo_3339_) as u8);
    v_res_3348_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl(
        v_00_u03b1_3336_,
        v_binderName_3337_,
        v_type_3338_,
        v_binderInfo_boxed_3347_,
        v_k_3340_,
        v_a_3341_,
        v_a_3342_,
        v_a_3343_,
        v_a_3344_,
        v_a_3345_,
    );
    leanh::lean_dec(v_a_3345_);
    leanh::lean_dec_ref(v_a_3344_);
    leanh::lean_dec(v_a_3343_);
    leanh::lean_dec_ref(v_a_3342_);
    leanh::lean_dec_ref(v_a_3341_);
    return v_res_3348_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(
    mut v_declName_3352_: *mut leanh::LeanObject,
    mut v_us_3353_: *mut leanh::LeanObject,
    mut v_a_3354_: *mut leanh::LeanObject,
    mut v_a_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v_val_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v_a_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v_a_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3387_: u8 = 0;
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3359_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___closed__1;
                v___x_3360_ = lean_name_eq(v_declName_3352_, v___x_3359_);
                if v___x_3360_ == 0 {
                    v___x_3361_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_3354_);
                    if leanh::lean_obj_tag(v___x_3361_) == 0 {
                        v_a_3362_ = leanh::lean_ctor_get(v___x_3361_, 0);
                        leanh::lean_inc(v_a_3362_);
                        leanh::lean_dec_ref_known(v___x_3361_, 1);
                        v___x_3363_ = (leanh::lean_unbox(v_a_3362_) as u8);
                        leanh::lean_dec(v_a_3362_);
                        leanh::lean_inc(v_declName_3352_);
                        v___x_3364_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                            v_declName_3352_,
                            v___x_3363_,
                            v_a_3356_,
                            v_a_3357_,
                        );
                        if leanh::lean_obj_tag(v___x_3364_) == 0 {
                            v_a_3365_ = leanh::lean_ctor_get(v___x_3364_, 0);
                            v_isSharedCheck_3375_ =
                                (!leanh::lean_is_exclusive(v___x_3364_)) as u8;
                            if v_isSharedCheck_3375_ == 0 {
                                v___x_3367_ = v___x_3364_;
                                v_isShared_3368_ = v_isSharedCheck_3375_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3365_);
                                leanh::lean_dec(v___x_3364_);
                                v___x_3367_ = leanh::lean_box(0);
                                v_isShared_3368_ = v_isSharedCheck_3375_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_us_3353_);
                            leanh::lean_dec(v_declName_3352_);
                            v_a_3376_ = leanh::lean_ctor_get(v___x_3364_, 0);
                            v_isSharedCheck_3383_ =
                                (!leanh::lean_is_exclusive(v___x_3364_)) as u8;
                            if v_isSharedCheck_3383_ == 0 {
                                v___x_3378_ = v___x_3364_;
                                v_isShared_3379_ = v_isSharedCheck_3383_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3376_);
                                leanh::lean_dec(v___x_3364_);
                                v___x_3378_ = leanh::lean_box(0);
                                v_isShared_3379_ = v_isSharedCheck_3383_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_us_3353_);
                        leanh::lean_dec(v_declName_3352_);
                        v_a_3384_ = leanh::lean_ctor_get(v___x_3361_, 0);
                        v_isSharedCheck_3391_ =
                            (!leanh::lean_is_exclusive(v___x_3361_)) as u8;
                        if v_isSharedCheck_3391_ == 0 {
                            v___x_3386_ = v___x_3361_;
                            v_isShared_3387_ = v_isSharedCheck_3391_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3384_);
                            leanh::lean_dec(v___x_3361_);
                            v___x_3386_ = leanh::lean_box(0);
                            v_isShared_3387_ = v_isSharedCheck_3391_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_us_3353_);
                    leanh::lean_dec(v_declName_3352_);
                    v___x_3392_ = l_Lean_Compiler_LCNF_erasedExpr;
                    v___x_3393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3393_, 0, v___x_3392_);
                    return v___x_3393_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3365_) == 1 {
                    leanh::lean_dec(v_declName_3352_);
                    v_val_3369_ = leanh::lean_ctor_get(v_a_3365_, 0);
                    leanh::lean_inc(v_val_3369_);
                    leanh::lean_dec_ref_known(v_a_3365_, 1);
                    v___x_3370_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(
                        v_val_3369_,
                        v_us_3353_,
                    );
                    if v_isShared_3368_ == 0 {
                        leanh::lean_ctor_set(v___x_3367_, 0, v___x_3370_);
                        v___x_3372_ = v___x_3367_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
                        v___x_3372_ = v_reuseFailAlloc_3373_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3367_);
                    leanh::lean_dec(v_a_3365_);
                    v___x_3374_ = l_Lean_Compiler_LCNF_getOtherDeclType(
                        v_declName_3352_,
                        v_us_3353_,
                        v_a_3354_,
                        v_a_3355_,
                        v_a_3356_,
                        v_a_3357_,
                    );
                    return v___x_3374_;
                }
            }
            2 => {
                return v___x_3372_;
            }
            3 => {
                if v_isShared_3379_ == 0 {
                    v___x_3381_ = v___x_3378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
                    v___x_3381_ = v_reuseFailAlloc_3382_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3381_;
            }
            5 => {
                if v_isShared_3387_ == 0 {
                    v___x_3389_ = v___x_3386_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
                    v___x_3389_ = v_reuseFailAlloc_3390_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferConstType___boxed(
    mut v_declName_3394_: *mut leanh::LeanObject,
    mut v_us_3395_: *mut leanh::LeanObject,
    mut v_a_3396_: *mut leanh::LeanObject,
    mut v_a_3397_: *mut leanh::LeanObject,
    mut v_a_3398_: *mut leanh::LeanObject,
    mut v_a_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(
        v_declName_3394_,
        v_us_3395_,
        v_a_3396_,
        v_a_3397_,
        v_a_3398_,
        v_a_3399_,
    );
    leanh::lean_dec(v_a_3399_);
    leanh::lean_dec_ref(v_a_3398_);
    leanh::lean_dec(v_a_3397_);
    leanh::lean_dec_ref(v_a_3396_);
    return v_res_3401_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = leanh::lean_box(0);
    v___x_3406_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__1;
    v___x_3407_ = l_Lean_mkConst(v___x_3406_, v___x_3405_);
    return v___x_3407_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = leanh::lean_box(0);
    v___x_3412_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__4;
    v___x_3413_ = l_Lean_mkConst(v___x_3412_, v___x_3411_);
    return v___x_3413_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = leanh::lean_box(0);
    v___x_3418_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__7;
    v___x_3419_ = l_Lean_mkConst(v___x_3418_, v___x_3417_);
    return v___x_3419_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3423_ = leanh::lean_box(0);
    v___x_3424_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__10;
    v___x_3425_ = l_Lean_mkConst(v___x_3424_, v___x_3423_);
    return v___x_3425_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = leanh::lean_box(0);
    v___x_3430_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__13;
    v___x_3431_ = l_Lean_mkConst(v___x_3430_, v___x_3429_);
    return v___x_3431_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3435_ = leanh::lean_box(0);
    v___x_3436_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__16;
    v___x_3437_ = l_Lean_mkConst(v___x_3436_, v___x_3435_);
    return v___x_3437_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = leanh::lean_box(0);
    v___x_3442_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__19;
    v___x_3443_ = l_Lean_mkConst(v___x_3442_, v___x_3441_);
    return v___x_3443_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(
    mut v_value_3444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_value_3444_) {
        0 => {
            let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3445_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__2,
            );
            return v___x_3445_;
        }
        1 => {
            let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3446_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__5,
            );
            return v___x_3446_;
        }
        2 => {
            let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3447_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__8,
            );
            return v___x_3447_;
        }
        3 => {
            let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3448_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__11,
            );
            return v___x_3448_;
        }
        4 => {
            let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3449_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__14,
            );
            return v___x_3449_;
        }
        5 => {
            let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3450_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__17,
            );
            return v___x_3450_;
        }
        _ => {
            let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3451_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___closed__20,
            );
            return v___x_3451_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType___boxed(
    mut v_value_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3453_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_3452_);
    leanh::lean_dec_ref(v_value_3452_);
    return v_res_3453_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(
    mut v___y_3454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v_r_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3486_: u8 = 0;
    let mut v_unused_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3456_ = lean_st_ref_get(v___y_3454_);
                v_ngen_3457_ = leanh::lean_ctor_get(v___x_3456_, 2);
                leanh::lean_inc_ref(v_ngen_3457_);
                leanh::lean_dec(v___x_3456_);
                v_namePrefix_3458_ = leanh::lean_ctor_get(v_ngen_3457_, 0);
                v_idx_3459_ = leanh::lean_ctor_get(v_ngen_3457_, 1);
                v_isSharedCheck_3488_ = (!leanh::lean_is_exclusive(v_ngen_3457_)) as u8;
                if v_isSharedCheck_3488_ == 0 {
                    v___x_3461_ = v_ngen_3457_;
                    v_isShared_3462_ = v_isSharedCheck_3488_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_3459_);
                    leanh::lean_inc(v_namePrefix_3458_);
                    leanh::lean_dec(v_ngen_3457_);
                    v___x_3461_ = leanh::lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3463_ = lean_st_ref_take(v___y_3454_);
                v_env_3464_ = leanh::lean_ctor_get(v___x_3463_, 0);
                v_nextMacroScope_3465_ = leanh::lean_ctor_get(v___x_3463_, 1);
                v_auxDeclNGen_3466_ = leanh::lean_ctor_get(v___x_3463_, 3);
                v_traceState_3467_ = leanh::lean_ctor_get(v___x_3463_, 4);
                v_cache_3468_ = leanh::lean_ctor_get(v___x_3463_, 5);
                v_messages_3469_ = leanh::lean_ctor_get(v___x_3463_, 6);
                v_infoState_3470_ = leanh::lean_ctor_get(v___x_3463_, 7);
                v_snapshotTasks_3471_ = leanh::lean_ctor_get(v___x_3463_, 8);
                v_isSharedCheck_3486_ = (!leanh::lean_is_exclusive(v___x_3463_)) as u8;
                if v_isSharedCheck_3486_ == 0 {
                    v_unused_3487_ = leanh::lean_ctor_get(v___x_3463_, 2);
                    leanh::lean_dec(v_unused_3487_);
                    v___x_3473_ = v___x_3463_;
                    v_isShared_3474_ = v_isSharedCheck_3486_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3471_);
                    leanh::lean_inc(v_infoState_3470_);
                    leanh::lean_inc(v_messages_3469_);
                    leanh::lean_inc(v_cache_3468_);
                    leanh::lean_inc(v_traceState_3467_);
                    leanh::lean_inc(v_auxDeclNGen_3466_);
                    leanh::lean_inc(v_nextMacroScope_3465_);
                    leanh::lean_inc(v_env_3464_);
                    leanh::lean_dec(v___x_3463_);
                    v___x_3473_ = leanh::lean_box(0);
                    v_isShared_3474_ = v_isSharedCheck_3486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_3459_);
                leanh::lean_inc(v_namePrefix_3458_);
                v_r_3475_ = l_Lean_Name_num___override(v_namePrefix_3458_, v_idx_3459_);
                v___x_3476_ = leanh::lean_unsigned_to_nat(1);
                v___x_3477_ = lean_nat_add(v_idx_3459_, v___x_3476_);
                leanh::lean_dec(v_idx_3459_);
                if v_isShared_3462_ == 0 {
                    leanh::lean_ctor_set(v___x_3461_, 1, v___x_3477_);
                    v___x_3479_ = v___x_3461_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_namePrefix_3458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3485_, 1, v___x_3477_);
                    v___x_3479_ = v_reuseFailAlloc_3485_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3474_ == 0 {
                    leanh::lean_ctor_set(v___x_3473_, 2, v___x_3479_);
                    v___x_3481_ = v___x_3473_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_env_3464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_nextMacroScope_3465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 2, v___x_3479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_auxDeclNGen_3466_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_traceState_3467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 5, v_cache_3468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 6, v_messages_3469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 7, v_infoState_3470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 8, v_snapshotTasks_3471_);
                    v___x_3481_ = v_reuseFailAlloc_3484_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3482_ = lean_st_ref_set(v___y_3454_, v___x_3481_);
                v___x_3483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3483_, 0, v_r_3475_);
                return v___x_3483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg___boxed(
    mut v___y_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3491_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_3489_);
    leanh::lean_dec(v___y_3489_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(
    mut v___y_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
    mut v___y_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3502_: u8 = 0;
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3498_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_3496_);
                v_a_3499_ = leanh::lean_ctor_get(v___x_3498_, 0);
                v_isSharedCheck_3506_ = (!leanh::lean_is_exclusive(v___x_3498_)) as u8;
                if v_isSharedCheck_3506_ == 0 {
                    v___x_3501_ = v___x_3498_;
                    v_isShared_3502_ = v_isSharedCheck_3506_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3499_);
                    leanh::lean_dec(v___x_3498_);
                    v___x_3501_ = leanh::lean_box(0);
                    v_isShared_3502_ = v_isSharedCheck_3506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3502_ == 0 {
                    v___x_3504_ = v___x_3501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
                    v___x_3504_ = v_reuseFailAlloc_3505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0___boxed(
    mut v___y_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3513_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
    leanh::lean_dec(v___y_3511_);
    leanh::lean_dec_ref(v___y_3510_);
    leanh::lean_dec(v___y_3509_);
    leanh::lean_dec_ref(v___y_3508_);
    leanh::lean_dec_ref(v___y_3507_);
    return v_res_3513_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(
    mut v_msg_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
    mut v___y_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849__overap_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1,
    );
    v_toApplicative_3522_ = leanh::lean_ctor_get(v___x_3521_, 0);
    v_toFunctor_3523_ = leanh::lean_ctor_get(v_toApplicative_3522_, 0);
    v_toSeq_3524_ = leanh::lean_ctor_get(v_toApplicative_3522_, 2);
    v_toSeqLeft_3525_ = leanh::lean_ctor_get(v_toApplicative_3522_, 3);
    v_toSeqRight_3526_ = leanh::lean_ctor_get(v_toApplicative_3522_, 4);
    v___f_3527_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2;
    v___f_3528_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3;
    leanh::lean_inc_ref_n(v_toFunctor_3523_, 2);
    v___f_3529_ = leanh::lean_alloc_closure(
        l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3529_, 0, v_toFunctor_3523_);
    v___f_3530_ = leanh::lean_alloc_closure(
        l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3530_, 0, v_toFunctor_3523_);
    v___x_3531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3531_, 0, v___f_3529_);
    leanh::lean_ctor_set(v___x_3531_, 1, v___f_3530_);
    leanh::lean_inc(v_toSeqRight_3526_);
    v___f_3532_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3532_, 0, v_toSeqRight_3526_);
    leanh::lean_inc(v_toSeqLeft_3525_);
    v___f_3533_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3533_, 0, v_toSeqLeft_3525_);
    leanh::lean_inc(v_toSeq_3524_);
    v___f_3534_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3534_, 0, v_toSeq_3524_);
    v___x_3535_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3535_, 0, v___x_3531_);
    leanh::lean_ctor_set(v___x_3535_, 1, v___f_3527_);
    leanh::lean_ctor_set(v___x_3535_, 2, v___f_3534_);
    leanh::lean_ctor_set(v___x_3535_, 3, v___f_3533_);
    leanh::lean_ctor_set(v___x_3535_, 4, v___f_3532_);
    v___x_3536_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3536_, 0, v___x_3535_);
    leanh::lean_ctor_set(v___x_3536_, 1, v___f_3528_);
    v___x_3537_ = l_StateRefT_x27_instMonad___redArg(v___x_3536_);
    v___x_3538_ = l_Lean_instInhabitedExpr;
    v___x_3539_ = l_instInhabitedOfMonad___redArg(v___x_3537_, v___x_3538_);
    v___f_3540_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3540_, 0, v___x_3539_);
    v___f_3541_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3541_, 0, v___f_3540_);
    v___x_6849__overap_3542_ = lean_panic_fn_borrowed(v___f_3541_, v_msg_3514_);
    leanh::lean_dec_ref(v___f_3541_);
    leanh::lean_inc(v___y_3519_);
    leanh::lean_inc_ref(v___y_3518_);
    leanh::lean_inc(v___y_3517_);
    leanh::lean_inc_ref(v___y_3516_);
    leanh::lean_inc_ref(v___y_3515_);
    v___x_3543_ = leanh::lean_apply_6(
        v___x_6849__overap_3542_,
        v___y_3515_,
        v___y_3516_,
        v___y_3517_,
        v___y_3518_,
        v___y_3519_,
        leanh::lean_box(0),
    );
    return v___x_3543_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2___boxed(
    mut v_msg_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
    mut v___y_3547_: *mut leanh::LeanObject,
    mut v___y_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(
        v_msg_3544_,
        v___y_3545_,
        v___y_3546_,
        v___y_3547_,
        v___y_3548_,
        v___y_3549_,
    );
    leanh::lean_dec(v___y_3549_);
    leanh::lean_dec_ref(v___y_3548_);
    leanh::lean_dec(v___y_3547_);
    leanh::lean_dec_ref(v___y_3546_);
    leanh::lean_dec_ref(v___y_3545_);
    return v_res_3551_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3552_ = l_Lean_Compiler_LCNF_anyExpr;
    v___x_3553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3553_, 0, v___x_3552_);
    return v___x_3553_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(
    mut v_upperBound_3554_: *mut leanh::LeanObject,
    mut v___x_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_b_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v_fst_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3574_: u8 = 0;
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_unused_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3564_ = lean_nat_dec_lt(v_a_3556_, v_upperBound_3554_);
                if v___x_3564_ == 0 {
                    leanh::lean_dec(v_a_3556_);
                    v___x_3565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3565_, 0, v_b_3557_);
                    return v___x_3565_;
                } else {
                    v_snd_3566_ = leanh::lean_ctor_get(v_b_3557_, 1);
                    v_isSharedCheck_3602_ = (!leanh::lean_is_exclusive(v_b_3557_)) as u8;
                    if v_isSharedCheck_3602_ == 0 {
                        v_unused_3603_ = leanh::lean_ctor_get(v_b_3557_, 0);
                        leanh::lean_dec(v_unused_3603_);
                        v___x_3568_ = v_b_3557_;
                        v_isShared_3569_ = v_isSharedCheck_3602_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3566_);
                        leanh::lean_dec(v_b_3557_);
                        v___x_3568_ = leanh::lean_box(0);
                        v_isShared_3569_ = v_isSharedCheck_3602_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3561_ = leanh::lean_unsigned_to_nat(1);
                v___x_3562_ = lean_nat_add(v_a_3556_, v___x_3561_);
                leanh::lean_dec(v_a_3556_);
                v_a_3556_ = v___x_3562_;
                v_b_3557_ = v_a_3560_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3570_ = leanh::lean_ctor_get(v_snd_3566_, 0);
                v_snd_3571_ = leanh::lean_ctor_get(v_snd_3566_, 1);
                v_isSharedCheck_3601_ = (!leanh::lean_is_exclusive(v_snd_3566_)) as u8;
                if v_isSharedCheck_3601_ == 0 {
                    v___x_3573_ = v_snd_3566_;
                    v_isShared_3574_ = v_isSharedCheck_3601_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3571_);
                    leanh::lean_inc(v_fst_3570_);
                    leanh::lean_dec(v_snd_3566_);
                    v___x_3573_ = leanh::lean_box(0);
                    v_isShared_3574_ = v_isSharedCheck_3601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3575_ = leanh::lean_box(0);
                v___x_3576_ = l_Lean_Expr_headBeta(v_snd_3571_);
                if leanh::lean_obj_tag(v___x_3576_) == 7 {
                    v_body_3577_ = leanh::lean_ctor_get(v___x_3576_, 2);
                    leanh::lean_inc_ref(v_body_3577_);
                    leanh::lean_dec_ref_known(v___x_3576_, 3);
                    if v_isShared_3574_ == 0 {
                        leanh::lean_ctor_set(v___x_3573_, 1, v_body_3577_);
                        v___x_3579_ = v___x_3573_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3583_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_fst_3570_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_body_3577_);
                        v___x_3579_ = v_reuseFailAlloc_3583_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3584_ = lean_expr_instantiate_rev_range(
                        v___x_3576_,
                        v_fst_3570_,
                        v_a_3556_,
                        v___x_3555_,
                    );
                    leanh::lean_dec_ref(v___x_3576_);
                    v___x_3585_ = l_Lean_Expr_headBeta(v___x_3584_);
                    if leanh::lean_obj_tag(v___x_3585_) == 7 {
                        leanh::lean_dec(v_fst_3570_);
                        v_body_3586_ = leanh::lean_ctor_get(v___x_3585_, 2);
                        leanh::lean_inc_ref(v_body_3586_);
                        leanh::lean_dec_ref_known(v___x_3585_, 3);
                        leanh::lean_inc(v_a_3556_);
                        if v_isShared_3574_ == 0 {
                            leanh::lean_ctor_set(v___x_3573_, 1, v_body_3586_);
                            leanh::lean_ctor_set(v___x_3573_, 0, v_a_3556_);
                            v___x_3588_ = v___x_3573_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3592_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3556_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_body_3586_);
                            v___x_3588_ = v_reuseFailAlloc_3592_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3556_);
                        v___x_3593_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
                        if v_isShared_3574_ == 0 {
                            leanh::lean_ctor_set(v___x_3573_, 1, v___x_3585_);
                            v___x_3595_ = v___x_3573_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3600_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_fst_3570_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3585_);
                            v___x_3595_ = v_reuseFailAlloc_3600_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3569_ == 0 {
                    leanh::lean_ctor_set(v___x_3568_, 1, v___x_3579_);
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3575_);
                    v___x_3581_ = v___x_3568_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3582_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3579_);
                    v___x_3581_ = v_reuseFailAlloc_3582_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_3560_ = v___x_3581_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_3569_ == 0 {
                    leanh::lean_ctor_set(v___x_3568_, 1, v___x_3588_);
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3575_);
                    v___x_3590_ = v___x_3568_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3588_);
                    v___x_3590_ = v_reuseFailAlloc_3591_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_3560_ = v___x_3590_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_3569_ == 0 {
                    leanh::lean_ctor_set(v___x_3568_, 1, v___x_3595_);
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3593_);
                    v___x_3597_ = v___x_3568_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 1, v___x_3595_);
                    v___x_3597_ = v_reuseFailAlloc_3599_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3598_, 0, v___x_3597_);
                return v___x_3598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___boxed(
    mut v_upperBound_3604_: *mut leanh::LeanObject,
    mut v___x_3605_: *mut leanh::LeanObject,
    mut v_a_3606_: *mut leanh::LeanObject,
    mut v_b_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_3604_, v___x_3605_, v_a_3606_, v_b_3607_);
    leanh::lean_dec_ref(v___x_3605_);
    leanh::lean_dec(v_upperBound_3604_);
    return v_res_3609_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = leanh::lean_box(0);
    v_dummy_3613_ = l_Lean_Expr_sort___override(v___x_3612_);
    return v_dummy_3613_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(
    mut v_e_3614_: *mut leanh::LeanObject,
    mut v_a_3615_: *mut leanh::LeanObject,
    mut v_a_3616_: *mut leanh::LeanObject,
    mut v_a_3617_: *mut leanh::LeanObject,
    mut v_a_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v_fst_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3621_ = l_Lean_Expr_getAppFn(v_e_3614_);
                v___x_3622_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
                    v___x_3621_,
                    v_a_3615_,
                    v_a_3616_,
                    v_a_3617_,
                    v_a_3618_,
                    v_a_3619_,
                );
                if leanh::lean_obj_tag(v___x_3622_) == 0 {
                    v_a_3623_ = leanh::lean_ctor_get(v___x_3622_, 0);
                    leanh::lean_inc(v_a_3623_);
                    leanh::lean_dec_ref_known(v___x_3622_, 1);
                    v_dummy_3624_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0,
                    );
                    v_nargs_3625_ = l_Lean_Expr_getAppNumArgs(v_e_3614_);
                    leanh::lean_inc(v_nargs_3625_);
                    v___x_3626_ = lean_mk_array(v_nargs_3625_, v_dummy_3624_);
                    v___x_3627_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3628_ = lean_nat_sub(v_nargs_3625_, v___x_3627_);
                    leanh::lean_dec(v_nargs_3625_);
                    v___x_3629_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_3614_,
                        v___x_3626_,
                        v___x_3628_,
                    );
                    v___x_3630_ = lean_array_get_size(v___x_3629_);
                    v___x_3631_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3632_ = leanh::lean_box(0);
                    v___x_3633_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3633_, 0, v___x_3631_);
                    leanh::lean_ctor_set(v___x_3633_, 1, v_a_3623_);
                    v___x_3634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3634_, 0, v___x_3632_);
                    leanh::lean_ctor_set(v___x_3634_, 1, v___x_3633_);
                    v___x_3635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v___x_3630_, v___x_3629_, v___x_3631_, v___x_3634_);
                    if leanh::lean_obj_tag(v___x_3635_) == 0 {
                        v_a_3636_ = leanh::lean_ctor_get(v___x_3635_, 0);
                        v_isSharedCheck_3653_ =
                            (!leanh::lean_is_exclusive(v___x_3635_)) as u8;
                        if v_isSharedCheck_3653_ == 0 {
                            v___x_3638_ = v___x_3635_;
                            v_isShared_3639_ = v_isSharedCheck_3653_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3636_);
                            leanh::lean_dec(v___x_3635_);
                            v___x_3638_ = leanh::lean_box(0);
                            v_isShared_3639_ = v_isSharedCheck_3653_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3629_);
                        v_a_3654_ = leanh::lean_ctor_get(v___x_3635_, 0);
                        v_isSharedCheck_3661_ =
                            (!leanh::lean_is_exclusive(v___x_3635_)) as u8;
                        if v_isSharedCheck_3661_ == 0 {
                            v___x_3656_ = v___x_3635_;
                            v_isShared_3657_ = v_isSharedCheck_3661_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3654_);
                            leanh::lean_dec(v___x_3635_);
                            v___x_3656_ = leanh::lean_box(0);
                            v_isShared_3657_ = v_isSharedCheck_3661_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3614_);
                    return v___x_3622_;
                }
            }
            1 => {
                v_fst_3640_ = leanh::lean_ctor_get(v_a_3636_, 0);
                if leanh::lean_obj_tag(v_fst_3640_) == 0 {
                    v_snd_3641_ = leanh::lean_ctor_get(v_a_3636_, 1);
                    leanh::lean_inc(v_snd_3641_);
                    leanh::lean_dec(v_a_3636_);
                    v_fst_3642_ = leanh::lean_ctor_get(v_snd_3641_, 0);
                    leanh::lean_inc(v_fst_3642_);
                    v_snd_3643_ = leanh::lean_ctor_get(v_snd_3641_, 1);
                    leanh::lean_inc(v_snd_3643_);
                    leanh::lean_dec(v_snd_3641_);
                    v___x_3644_ = lean_expr_instantiate_rev_range(
                        v_snd_3643_,
                        v_fst_3642_,
                        v___x_3630_,
                        v___x_3629_,
                    );
                    leanh::lean_dec_ref(v___x_3629_);
                    leanh::lean_dec(v_fst_3642_);
                    leanh::lean_dec(v_snd_3643_);
                    v___x_3645_ = l_Lean_Expr_headBeta(v___x_3644_);
                    if v_isShared_3639_ == 0 {
                        leanh::lean_ctor_set(v___x_3638_, 0, v___x_3645_);
                        v___x_3647_ = v___x_3638_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3648_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
                        v___x_3647_ = v_reuseFailAlloc_3648_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3640_);
                    leanh::lean_dec(v_a_3636_);
                    leanh::lean_dec_ref(v___x_3629_);
                    v_val_3649_ = leanh::lean_ctor_get(v_fst_3640_, 0);
                    leanh::lean_inc(v_val_3649_);
                    leanh::lean_dec_ref_known(v_fst_3640_, 1);
                    if v_isShared_3639_ == 0 {
                        leanh::lean_ctor_set(v___x_3638_, 0, v_val_3649_);
                        v___x_3651_ = v___x_3638_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_val_3649_);
                        v___x_3651_ = v_reuseFailAlloc_3652_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3647_;
            }
            3 => {
                return v___x_3651_;
            }
            4 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(
    mut v_e_3662_: *mut leanh::LeanObject,
    mut v_fvars_3663_: *mut leanh::LeanObject,
    mut v_all_3664_: *mut leanh::LeanObject,
    mut v_a_3665_: *mut leanh::LeanObject,
    mut v_a_3666_: *mut leanh::LeanObject,
    mut v_a_3667_: *mut leanh::LeanObject,
    mut v_a_3668_: *mut leanh::LeanObject,
    mut v_a_3669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3674_: u8 = 0;
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_declName_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3707_: u8 = 0;
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_3662_) {
                6 => {
                    v_binderName_3671_ = leanh::lean_ctor_get(v_e_3662_, 0);
                    leanh::lean_inc(v_binderName_3671_);
                    v_binderType_3672_ = leanh::lean_ctor_get(v_e_3662_, 1);
                    leanh::lean_inc_ref(v_binderType_3672_);
                    v_body_3673_ = leanh::lean_ctor_get(v_e_3662_, 2);
                    leanh::lean_inc_ref(v_body_3673_);
                    v_binderInfo_3674_ = leanh::lean_ctor_get_uint8(
                        v_e_3662_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_e_3662_, 3);
                    v___x_3675_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
                    if leanh::lean_obj_tag(v___x_3675_) == 0 {
                        v_a_3676_ = leanh::lean_ctor_get(v___x_3675_, 0);
                        leanh::lean_inc_n(v_a_3676_, 2);
                        leanh::lean_dec_ref_known(v___x_3675_, 1);
                        v___x_3677_ = lean_expr_instantiate_rev(v_binderType_3672_, v_all_3664_);
                        leanh::lean_dec_ref(v_binderType_3672_);
                        v___x_3678_ = l_Lean_Expr_fvar___override(v_a_3676_);
                        v___x_3679_ = 0;
                        v___x_3680_ = l_Lean_LocalContext_mkLocalDecl(
                            v_a_3665_,
                            v_a_3676_,
                            v_binderName_3671_,
                            v___x_3677_,
                            v_binderInfo_3674_,
                            v___x_3679_,
                        );
                        leanh::lean_inc_ref(v___x_3678_);
                        v___x_3681_ = lean_array_push(v_fvars_3663_, v___x_3678_);
                        v___x_3682_ = lean_array_push(v_all_3664_, v___x_3678_);
                        v_e_3662_ = v_body_3673_;
                        v_fvars_3663_ = v___x_3681_;
                        v_all_3664_ = v___x_3682_;
                        v_a_3665_ = v___x_3680_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_body_3673_);
                        leanh::lean_dec_ref(v_binderType_3672_);
                        leanh::lean_dec(v_binderName_3671_);
                        leanh::lean_dec_ref(v_a_3665_);
                        leanh::lean_dec_ref(v_all_3664_);
                        leanh::lean_dec_ref(v_fvars_3663_);
                        v_a_3684_ = leanh::lean_ctor_get(v___x_3675_, 0);
                        v_isSharedCheck_3691_ =
                            (!leanh::lean_is_exclusive(v___x_3675_)) as u8;
                        if v_isSharedCheck_3691_ == 0 {
                            v___x_3686_ = v___x_3675_;
                            v_isShared_3687_ = v_isSharedCheck_3691_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3684_);
                            leanh::lean_dec(v___x_3675_);
                            v___x_3686_ = leanh::lean_box(0);
                            v_isShared_3687_ = v_isSharedCheck_3691_;
                            state = 1;
                            continue;
                        }
                    }
                }
                8 => {
                    v_declName_3692_ = leanh::lean_ctor_get(v_e_3662_, 0);
                    leanh::lean_inc(v_declName_3692_);
                    v_type_3693_ = leanh::lean_ctor_get(v_e_3662_, 1);
                    leanh::lean_inc_ref(v_type_3693_);
                    v_body_3694_ = leanh::lean_ctor_get(v_e_3662_, 3);
                    leanh::lean_inc_ref(v_body_3694_);
                    leanh::lean_dec_ref_known(v_e_3662_, 4);
                    v___x_3695_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
                    if leanh::lean_obj_tag(v___x_3695_) == 0 {
                        v_a_3696_ = leanh::lean_ctor_get(v___x_3695_, 0);
                        leanh::lean_inc_n(v_a_3696_, 2);
                        leanh::lean_dec_ref_known(v___x_3695_, 1);
                        v___x_3697_ = lean_expr_instantiate_rev(v_type_3693_, v_all_3664_);
                        leanh::lean_dec_ref(v_type_3693_);
                        v___x_3698_ = 0;
                        v___x_3699_ = l_Lean_Expr_fvar___override(v_a_3696_);
                        v___x_3700_ = 0;
                        v___x_3701_ = l_Lean_LocalContext_mkLocalDecl(
                            v_a_3665_,
                            v_a_3696_,
                            v_declName_3692_,
                            v___x_3697_,
                            v___x_3698_,
                            v___x_3700_,
                        );
                        v___x_3702_ = lean_array_push(v_all_3664_, v___x_3699_);
                        v_e_3662_ = v_body_3694_;
                        v_all_3664_ = v___x_3702_;
                        v_a_3665_ = v___x_3701_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_body_3694_);
                        leanh::lean_dec_ref(v_type_3693_);
                        leanh::lean_dec(v_declName_3692_);
                        leanh::lean_dec_ref(v_a_3665_);
                        leanh::lean_dec_ref(v_all_3664_);
                        leanh::lean_dec_ref(v_fvars_3663_);
                        v_a_3704_ = leanh::lean_ctor_get(v___x_3695_, 0);
                        v_isSharedCheck_3711_ =
                            (!leanh::lean_is_exclusive(v___x_3695_)) as u8;
                        if v_isSharedCheck_3711_ == 0 {
                            v___x_3706_ = v___x_3695_;
                            v_isShared_3707_ = v_isSharedCheck_3711_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3704_);
                            leanh::lean_dec(v___x_3695_);
                            v___x_3706_ = leanh::lean_box(0);
                            v_isShared_3707_ = v_isSharedCheck_3711_;
                            state = 3;
                            continue;
                        }
                    }
                }
                _ => {
                    v___x_3712_ = lean_expr_instantiate_rev(v_e_3662_, v_all_3664_);
                    leanh::lean_dec_ref(v_all_3664_);
                    leanh::lean_dec_ref(v_e_3662_);
                    v___x_3713_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
                        v___x_3712_,
                        v_a_3665_,
                        v_a_3666_,
                        v_a_3667_,
                        v_a_3668_,
                        v_a_3669_,
                    );
                    if leanh::lean_obj_tag(v___x_3713_) == 0 {
                        v_a_3714_ = leanh::lean_ctor_get(v___x_3713_, 0);
                        leanh::lean_inc(v_a_3714_);
                        leanh::lean_dec_ref_known(v___x_3713_, 1);
                        v___x_3715_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(
                            v_fvars_3663_,
                            v_a_3714_,
                            v_a_3665_,
                            v_a_3666_,
                            v_a_3667_,
                            v_a_3668_,
                            v_a_3669_,
                        );
                        leanh::lean_dec_ref(v_a_3665_);
                        leanh::lean_dec(v_a_3714_);
                        leanh::lean_dec_ref(v_fvars_3663_);
                        return v___x_3715_;
                    } else {
                        leanh::lean_dec_ref(v_a_3665_);
                        leanh::lean_dec_ref(v_fvars_3663_);
                        return v___x_3713_;
                    }
                }
            },
            1 => {
                if v_isShared_3687_ == 0 {
                    v___x_3689_ = v___x_3686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3689_;
            }
            3 => {
                if v_isShared_3707_ == 0 {
                    v___x_3709_ = v___x_3706_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
                    v___x_3709_ = v_reuseFailAlloc_3710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(
    mut v_e_3716_: *mut leanh::LeanObject,
    mut v_a_3717_: *mut leanh::LeanObject,
    mut v_a_3718_: *mut leanh::LeanObject,
    mut v_a_3719_: *mut leanh::LeanObject,
    mut v_a_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3723_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0;
    leanh::lean_inc_ref(v_a_3717_);
    v___x_3724_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_3716_, v___x_3723_, v___x_3723_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
    return v___x_3724_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2;
    v___x_3729_ = leanh::lean_unsigned_to_nat(73);
    v___x_3730_ = leanh::lean_unsigned_to_nat(135);
    v___x_3731_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__1;
    v___x_3732_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_3733_ = l_mkPanicMessageWithDecl(
        v___x_3732_,
        v___x_3731_,
        v___x_3730_,
        v___x_3729_,
        v___x_3728_,
    );
    return v___x_3733_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferType(
    mut v_e_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
    mut v_a_3738_: *mut leanh::LeanObject,
    mut v_a_3739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_3734_) {
        1 => {
            let mut v_fvarId_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_3741_ = leanh::lean_ctor_get(v_e_3734_, 0);
            leanh::lean_inc(v_fvarId_3741_);
            leanh::lean_dec_ref_known(v_e_3734_, 1);
            v___x_3742_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(
                v_fvarId_3741_,
                v_a_3735_,
                v_a_3736_,
                v_a_3737_,
                v_a_3738_,
                v_a_3739_,
            );
            return v___x_3742_;
        }
        3 => {
            let mut v_u_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_u_3743_ = leanh::lean_ctor_get(v_e_3734_, 0);
            leanh::lean_inc(v_u_3743_);
            leanh::lean_dec_ref_known(v_e_3734_, 1);
            v___x_3744_ = l_Lean_Level_succ___override(v_u_3743_);
            v___x_3745_ = l_Lean_Expr_sort___override(v___x_3744_);
            v___x_3746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3746_, 0, v___x_3745_);
            return v___x_3746_;
        }
        4 => {
            let mut v_declName_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_3747_ = leanh::lean_ctor_get(v_e_3734_, 0);
            leanh::lean_inc(v_declName_3747_);
            v_us_3748_ = leanh::lean_ctor_get(v_e_3734_, 1);
            leanh::lean_inc(v_us_3748_);
            leanh::lean_dec_ref_known(v_e_3734_, 2);
            v___x_3749_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(
                v_declName_3747_,
                v_us_3748_,
                v_a_3736_,
                v_a_3737_,
                v_a_3738_,
                v_a_3739_,
            );
            return v___x_3749_;
        }
        5 => {
            let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3750_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(
                v_e_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_,
            );
            return v___x_3750_;
        }
        6 => {
            let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3751_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(
                v_e_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_,
            );
            return v___x_3751_;
        }
        7 => {
            let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3752_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(
                v_e_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_,
            );
            return v___x_3752_;
        }
        _ => {
            let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_e_3734_);
            v___x_3753_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3),
                core::ptr::addr_of_mut!(
                    l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3_once
                ),
                _init_l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__3,
            );
            v___x_3754_ = l_panic___at___00Lean_Compiler_LCNF_InferType_Pure_inferType_spec__2(
                v___x_3753_,
                v_a_3735_,
                v_a_3736_,
                v_a_3737_,
                v_a_3738_,
                v_a_3739_,
            );
            return v___x_3754_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(
    mut v_type_3755_: *mut leanh::LeanObject,
    mut v_a_3756_: *mut leanh::LeanObject,
    mut v_a_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v_u_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3762_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
                    v_type_3755_,
                    v_a_3756_,
                    v_a_3757_,
                    v_a_3758_,
                    v_a_3759_,
                    v_a_3760_,
                );
                if leanh::lean_obj_tag(v___x_3762_) == 0 {
                    v_a_3763_ = leanh::lean_ctor_get(v___x_3762_, 0);
                    v_isSharedCheck_3776_ = (!leanh::lean_is_exclusive(v___x_3762_)) as u8;
                    if v_isSharedCheck_3776_ == 0 {
                        v___x_3765_ = v___x_3762_;
                        v_isShared_3766_ = v_isSharedCheck_3776_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3763_);
                        leanh::lean_dec(v___x_3762_);
                        v___x_3765_ = leanh::lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3776_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3777_ = leanh::lean_ctor_get(v___x_3762_, 0);
                    v_isSharedCheck_3784_ = (!leanh::lean_is_exclusive(v___x_3762_)) as u8;
                    if v_isSharedCheck_3784_ == 0 {
                        v___x_3779_ = v___x_3762_;
                        v_isShared_3780_ = v_isSharedCheck_3784_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3777_);
                        leanh::lean_dec(v___x_3762_);
                        v___x_3779_ = leanh::lean_box(0);
                        v_isShared_3780_ = v_isSharedCheck_3784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3763_) == 3 {
                    v_u_3767_ = leanh::lean_ctor_get(v_a_3763_, 0);
                    leanh::lean_inc(v_u_3767_);
                    leanh::lean_dec_ref_known(v_a_3763_, 1);
                    v___x_3768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3768_, 0, v_u_3767_);
                    if v_isShared_3766_ == 0 {
                        leanh::lean_ctor_set(v___x_3765_, 0, v___x_3768_);
                        v___x_3770_ = v___x_3765_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
                        v___x_3770_ = v_reuseFailAlloc_3771_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3763_);
                    v___x_3772_ = leanh::lean_box(0);
                    if v_isShared_3766_ == 0 {
                        leanh::lean_ctor_set(v___x_3765_, 0, v___x_3772_);
                        v___x_3774_ = v___x_3765_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
                        v___x_3774_ = v_reuseFailAlloc_3775_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3770_;
            }
            3 => {
                return v___x_3774_;
            }
            4 => {
                if v_isShared_3780_ == 0 {
                    v___x_3782_ = v___x_3779_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
                    v___x_3782_ = v_reuseFailAlloc_3783_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_Lean_Compiler_LCNF_erasedExpr;
    v___x_3786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(
    mut v_as_3787_: *mut leanh::LeanObject,
    mut v_sz_3788_: usize,
    mut v_i_3789_: usize,
    mut v_b_3790_: *mut leanh::LeanObject,
    mut v___y_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
    mut v___y_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_snd_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v_val_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: usize = 0;
    let mut v___x_3817_: usize = 0;
    let mut v_reuseFailAlloc_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3820_: u8 = 0;
    let mut v_unused_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_unused_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_a_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_a_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3797_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
                if v___x_3797_ == 0 {
                    v___x_3798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3798_, 0, v_b_3790_);
                    return v___x_3798_;
                } else {
                    v_a_3799_ = lean_array_uget_borrowed(v_as_3787_, v_i_3789_);
                    leanh::lean_inc(v_a_3799_);
                    v___x_3800_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
                        v_a_3799_,
                        v___y_3791_,
                        v___y_3792_,
                        v___y_3793_,
                        v___y_3794_,
                        v___y_3795_,
                    );
                    if leanh::lean_obj_tag(v___x_3800_) == 0 {
                        v_a_3801_ = leanh::lean_ctor_get(v___x_3800_, 0);
                        leanh::lean_inc(v_a_3801_);
                        leanh::lean_dec_ref_known(v___x_3800_, 1);
                        v___x_3802_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(
                            v_a_3801_,
                            v___y_3791_,
                            v___y_3792_,
                            v___y_3793_,
                            v___y_3794_,
                            v___y_3795_,
                        );
                        if leanh::lean_obj_tag(v___x_3802_) == 0 {
                            v_a_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
                            v_isSharedCheck_3835_ =
                                (!leanh::lean_is_exclusive(v___x_3802_)) as u8;
                            if v_isSharedCheck_3835_ == 0 {
                                v___x_3805_ = v___x_3802_;
                                v_isShared_3806_ = v_isSharedCheck_3835_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3803_);
                                leanh::lean_dec(v___x_3802_);
                                v___x_3805_ = leanh::lean_box(0);
                                v_isShared_3806_ = v_isSharedCheck_3835_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_3790_);
                            v_a_3836_ = leanh::lean_ctor_get(v___x_3802_, 0);
                            v_isSharedCheck_3843_ =
                                (!leanh::lean_is_exclusive(v___x_3802_)) as u8;
                            if v_isSharedCheck_3843_ == 0 {
                                v___x_3838_ = v___x_3802_;
                                v_isShared_3839_ = v_isSharedCheck_3843_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3836_);
                                leanh::lean_dec(v___x_3802_);
                                v___x_3838_ = leanh::lean_box(0);
                                v_isShared_3839_ = v_isSharedCheck_3843_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3790_);
                        v_a_3844_ = leanh::lean_ctor_get(v___x_3800_, 0);
                        v_isSharedCheck_3851_ =
                            (!leanh::lean_is_exclusive(v___x_3800_)) as u8;
                        if v_isSharedCheck_3851_ == 0 {
                            v___x_3846_ = v___x_3800_;
                            v_isShared_3847_ = v_isSharedCheck_3851_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3844_);
                            leanh::lean_dec(v___x_3800_);
                            v___x_3846_ = leanh::lean_box(0);
                            v_isShared_3847_ = v_isSharedCheck_3851_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3803_) == 1 {
                    leanh::lean_del_object(v___x_3805_);
                    v_snd_3807_ = leanh::lean_ctor_get(v_b_3790_, 1);
                    v_isSharedCheck_3820_ = (!leanh::lean_is_exclusive(v_b_3790_)) as u8;
                    if v_isSharedCheck_3820_ == 0 {
                        v_unused_3821_ = leanh::lean_ctor_get(v_b_3790_, 0);
                        leanh::lean_dec(v_unused_3821_);
                        v___x_3809_ = v_b_3790_;
                        v_isShared_3810_ = v_isSharedCheck_3820_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3807_);
                        leanh::lean_dec(v_b_3790_);
                        v___x_3809_ = leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3820_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3803_);
                    v_snd_3822_ = leanh::lean_ctor_get(v_b_3790_, 1);
                    v_isSharedCheck_3833_ = (!leanh::lean_is_exclusive(v_b_3790_)) as u8;
                    if v_isSharedCheck_3833_ == 0 {
                        v_unused_3834_ = leanh::lean_ctor_get(v_b_3790_, 0);
                        leanh::lean_dec(v_unused_3834_);
                        v___x_3824_ = v_b_3790_;
                        v_isShared_3825_ = v_isSharedCheck_3833_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3822_);
                        leanh::lean_dec(v_b_3790_);
                        v___x_3824_ = leanh::lean_box(0);
                        v_isShared_3825_ = v_isSharedCheck_3833_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_val_3811_ = leanh::lean_ctor_get(v_a_3803_, 0);
                leanh::lean_inc(v_val_3811_);
                leanh::lean_dec_ref_known(v_a_3803_, 1);
                v___x_3812_ = leanh::lean_box(0);
                v___x_3813_ = l_Lean_mkLevelIMax_x27(v_val_3811_, v_snd_3807_);
                if v_isShared_3810_ == 0 {
                    leanh::lean_ctor_set(v___x_3809_, 1, v___x_3813_);
                    leanh::lean_ctor_set(v___x_3809_, 0, v___x_3812_);
                    v___x_3815_ = v___x_3809_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3819_, 1, v___x_3813_);
                    v___x_3815_ = v_reuseFailAlloc_3819_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3816_ = 1usize;
                v___x_3817_ = lean_usize_add(v_i_3789_, v___x_3816_);
                v_i_3789_ = v___x_3817_;
                v_b_3790_ = v___x_3815_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
                if v_isShared_3825_ == 0 {
                    leanh::lean_ctor_set(v___x_3824_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3824_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_snd_3822_);
                    v___x_3828_ = v_reuseFailAlloc_3832_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3806_ == 0 {
                    leanh::lean_ctor_set(v___x_3805_, 0, v___x_3828_);
                    v___x_3830_ = v___x_3805_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
                    v___x_3830_ = v_reuseFailAlloc_3831_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3830_;
            }
            7 => {
                if v_isShared_3839_ == 0 {
                    v___x_3841_ = v___x_3838_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3841_;
            }
            9 => {
                if v_isShared_3847_ == 0 {
                    v___x_3849_ = v___x_3846_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(
    mut v_e_3852_: *mut leanh::LeanObject,
    mut v_fvars_3853_: *mut leanh::LeanObject,
    mut v_a_3854_: *mut leanh::LeanObject,
    mut v_a_3855_: *mut leanh::LeanObject,
    mut v_a_3856_: *mut leanh::LeanObject,
    mut v_a_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3863_: u8 = 0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: u8 = 0;
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_e_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v_val_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3890_: usize = 0;
    let mut v___x_3891_: usize = 0;
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v_fst_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_a_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v_a_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_3852_) == 7 {
                    v_binderName_3860_ = leanh::lean_ctor_get(v_e_3852_, 0);
                    leanh::lean_inc(v_binderName_3860_);
                    v_binderType_3861_ = leanh::lean_ctor_get(v_e_3852_, 1);
                    leanh::lean_inc_ref(v_binderType_3861_);
                    v_body_3862_ = leanh::lean_ctor_get(v_e_3852_, 2);
                    leanh::lean_inc_ref(v_body_3862_);
                    v_binderInfo_3863_ = leanh::lean_ctor_get_uint8(
                        v_e_3852_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_e_3852_, 3);
                    v___x_3864_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0(v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
                    if leanh::lean_obj_tag(v___x_3864_) == 0 {
                        v_a_3865_ = leanh::lean_ctor_get(v___x_3864_, 0);
                        leanh::lean_inc_n(v_a_3865_, 2);
                        leanh::lean_dec_ref_known(v___x_3864_, 1);
                        v___x_3866_ = lean_expr_instantiate_rev(v_binderType_3861_, v_fvars_3853_);
                        leanh::lean_dec_ref(v_binderType_3861_);
                        v___x_3867_ = l_Lean_Expr_fvar___override(v_a_3865_);
                        v___x_3868_ = 0;
                        v___x_3869_ = l_Lean_LocalContext_mkLocalDecl(
                            v_a_3854_,
                            v_a_3865_,
                            v_binderName_3860_,
                            v___x_3866_,
                            v_binderInfo_3863_,
                            v___x_3868_,
                        );
                        v___x_3870_ = lean_array_push(v_fvars_3853_, v___x_3867_);
                        v_e_3852_ = v_body_3862_;
                        v_fvars_3853_ = v___x_3870_;
                        v_a_3854_ = v___x_3869_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_body_3862_);
                        leanh::lean_dec_ref(v_binderType_3861_);
                        leanh::lean_dec(v_binderName_3860_);
                        leanh::lean_dec_ref(v_a_3854_);
                        leanh::lean_dec_ref(v_fvars_3853_);
                        v_a_3872_ = leanh::lean_ctor_get(v___x_3864_, 0);
                        v_isSharedCheck_3879_ =
                            (!leanh::lean_is_exclusive(v___x_3864_)) as u8;
                        if v_isSharedCheck_3879_ == 0 {
                            v___x_3874_ = v___x_3864_;
                            v_isShared_3875_ = v_isSharedCheck_3879_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3872_);
                            leanh::lean_dec(v___x_3864_);
                            v___x_3874_ = leanh::lean_box(0);
                            v_isShared_3875_ = v_isSharedCheck_3879_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_e_3880_ = lean_expr_instantiate_rev(v_e_3852_, v_fvars_3853_);
                    leanh::lean_dec_ref(v_e_3852_);
                    v___x_3881_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(
                        v_e_3880_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_,
                    );
                    if leanh::lean_obj_tag(v___x_3881_) == 0 {
                        v_a_3882_ = leanh::lean_ctor_get(v___x_3881_, 0);
                        v_isSharedCheck_3921_ =
                            (!leanh::lean_is_exclusive(v___x_3881_)) as u8;
                        if v_isSharedCheck_3921_ == 0 {
                            v___x_3884_ = v___x_3881_;
                            v_isShared_3885_ = v_isSharedCheck_3921_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3882_);
                            leanh::lean_dec(v___x_3881_);
                            v___x_3884_ = leanh::lean_box(0);
                            v_isShared_3885_ = v_isSharedCheck_3921_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_3854_);
                        leanh::lean_dec_ref(v_fvars_3853_);
                        v_a_3922_ = leanh::lean_ctor_get(v___x_3881_, 0);
                        v_isSharedCheck_3929_ =
                            (!leanh::lean_is_exclusive(v___x_3881_)) as u8;
                        if v_isSharedCheck_3929_ == 0 {
                            v___x_3924_ = v___x_3881_;
                            v_isShared_3925_ = v_isSharedCheck_3929_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3922_);
                            leanh::lean_dec(v___x_3881_);
                            v___x_3924_ = leanh::lean_box(0);
                            v_isShared_3925_ = v_isSharedCheck_3929_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3875_ == 0 {
                    v___x_3877_ = v___x_3874_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3878_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
                    v___x_3877_ = v_reuseFailAlloc_3878_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3877_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3882_) == 1 {
                    leanh::lean_del_object(v___x_3884_);
                    v_val_3886_ = leanh::lean_ctor_get(v_a_3882_, 0);
                    leanh::lean_inc(v_val_3886_);
                    leanh::lean_dec_ref_known(v_a_3882_, 1);
                    v___x_3887_ = l_Array_reverse___redArg(v_fvars_3853_);
                    v___x_3888_ = leanh::lean_box(0);
                    v___x_3889_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3889_, 0, v___x_3888_);
                    leanh::lean_ctor_set(v___x_3889_, 1, v_val_3886_);
                    v_sz_3890_ = lean_array_size(v___x_3887_);
                    v___x_3891_ = 0usize;
                    v___x_3892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v___x_3887_, v_sz_3890_, v___x_3891_, v___x_3889_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
                    leanh::lean_dec_ref(v_a_3854_);
                    leanh::lean_dec_ref(v___x_3887_);
                    if leanh::lean_obj_tag(v___x_3892_) == 0 {
                        v_a_3893_ = leanh::lean_ctor_get(v___x_3892_, 0);
                        v_isSharedCheck_3908_ =
                            (!leanh::lean_is_exclusive(v___x_3892_)) as u8;
                        if v_isSharedCheck_3908_ == 0 {
                            v___x_3895_ = v___x_3892_;
                            v_isShared_3896_ = v_isSharedCheck_3908_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3893_);
                            leanh::lean_dec(v___x_3892_);
                            v___x_3895_ = leanh::lean_box(0);
                            v_isShared_3896_ = v_isSharedCheck_3908_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3909_ = leanh::lean_ctor_get(v___x_3892_, 0);
                        v_isSharedCheck_3916_ =
                            (!leanh::lean_is_exclusive(v___x_3892_)) as u8;
                        if v_isSharedCheck_3916_ == 0 {
                            v___x_3911_ = v___x_3892_;
                            v_isShared_3912_ = v_isSharedCheck_3916_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3909_);
                            leanh::lean_dec(v___x_3892_);
                            v___x_3911_ = leanh::lean_box(0);
                            v_isShared_3912_ = v_isSharedCheck_3916_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3882_);
                    leanh::lean_dec_ref(v_a_3854_);
                    leanh::lean_dec_ref(v_fvars_3853_);
                    v___x_3917_ = l_Lean_Compiler_LCNF_erasedExpr;
                    if v_isShared_3885_ == 0 {
                        leanh::lean_ctor_set(v___x_3884_, 0, v___x_3917_);
                        v___x_3919_ = v___x_3884_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
                        v___x_3919_ = v_reuseFailAlloc_3920_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_3897_ = leanh::lean_ctor_get(v_a_3893_, 0);
                if leanh::lean_obj_tag(v_fst_3897_) == 0 {
                    v_snd_3898_ = leanh::lean_ctor_get(v_a_3893_, 1);
                    leanh::lean_inc(v_snd_3898_);
                    leanh::lean_dec(v_a_3893_);
                    v___x_3899_ = l_Lean_Level_normalize(v_snd_3898_);
                    leanh::lean_dec(v_snd_3898_);
                    v___x_3900_ = l_Lean_Expr_sort___override(v___x_3899_);
                    if v_isShared_3896_ == 0 {
                        leanh::lean_ctor_set(v___x_3895_, 0, v___x_3900_);
                        v___x_3902_ = v___x_3895_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3903_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                        v___x_3902_ = v_reuseFailAlloc_3903_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3897_);
                    leanh::lean_dec(v_a_3893_);
                    v_val_3904_ = leanh::lean_ctor_get(v_fst_3897_, 0);
                    leanh::lean_inc(v_val_3904_);
                    leanh::lean_dec_ref_known(v_fst_3897_, 1);
                    if v_isShared_3896_ == 0 {
                        leanh::lean_ctor_set(v___x_3895_, 0, v_val_3904_);
                        v___x_3906_ = v___x_3895_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_val_3904_);
                        v___x_3906_ = v_reuseFailAlloc_3907_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3902_;
            }
            6 => {
                return v___x_3906_;
            }
            7 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3915_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3914_;
            }
            9 => {
                return v___x_3919_;
            }
            10 => {
                if v_isShared_3925_ == 0 {
                    v___x_3927_ = v___x_3924_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
                    v___x_3927_ = v_reuseFailAlloc_3928_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(
    mut v_e_3930_: *mut leanh::LeanObject,
    mut v_a_3931_: *mut leanh::LeanObject,
    mut v_a_3932_: *mut leanh::LeanObject,
    mut v_a_3933_: *mut leanh::LeanObject,
    mut v_a_3934_: *mut leanh::LeanObject,
    mut v_a_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3937_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___closed__0;
    leanh::lean_inc_ref(v_a_3931_);
    v___x_3938_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_3930_, v___x_3937_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
    return v___x_3938_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferForallType___boxed(
    mut v_e_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_a_3942_: *mut leanh::LeanObject,
    mut v_a_3943_: *mut leanh::LeanObject,
    mut v_a_3944_: *mut leanh::LeanObject,
    mut v_a_3945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3946_ = l_Lean_Compiler_LCNF_InferType_Pure_inferForallType(
        v_e_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_,
    );
    leanh::lean_dec(v_a_3944_);
    leanh::lean_dec_ref(v_a_3943_);
    leanh::lean_dec(v_a_3942_);
    leanh::lean_dec_ref(v_a_3941_);
    leanh::lean_dec_ref(v_a_3940_);
    return v_res_3946_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType___boxed(
    mut v_e_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_a_3951_: *mut leanh::LeanObject,
    mut v_a_3952_: *mut leanh::LeanObject,
    mut v_a_3953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3954_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLambdaType(
        v_e_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_,
    );
    leanh::lean_dec(v_a_3952_);
    leanh::lean_dec_ref(v_a_3951_);
    leanh::lean_dec(v_a_3950_);
    leanh::lean_dec_ref(v_a_3949_);
    leanh::lean_dec_ref(v_a_3948_);
    return v_res_3954_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f___boxed(
    mut v_type_3955_: *mut leanh::LeanObject,
    mut v_a_3956_: *mut leanh::LeanObject,
    mut v_a_3957_: *mut leanh::LeanObject,
    mut v_a_3958_: *mut leanh::LeanObject,
    mut v_a_3959_: *mut leanh::LeanObject,
    mut v_a_3960_: *mut leanh::LeanObject,
    mut v_a_3961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3962_ = l_Lean_Compiler_LCNF_InferType_Pure_getLevel_x3f(
        v_type_3955_,
        v_a_3956_,
        v_a_3957_,
        v_a_3958_,
        v_a_3959_,
        v_a_3960_,
    );
    leanh::lean_dec(v_a_3960_);
    leanh::lean_dec_ref(v_a_3959_);
    leanh::lean_dec(v_a_3958_);
    leanh::lean_dec_ref(v_a_3957_);
    leanh::lean_dec_ref(v_a_3956_);
    return v_res_3962_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferType___boxed(
    mut v_e_3963_: *mut leanh::LeanObject,
    mut v_a_3964_: *mut leanh::LeanObject,
    mut v_a_3965_: *mut leanh::LeanObject,
    mut v_a_3966_: *mut leanh::LeanObject,
    mut v_a_3967_: *mut leanh::LeanObject,
    mut v_a_3968_: *mut leanh::LeanObject,
    mut v_a_3969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
        v_e_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_,
    );
    leanh::lean_dec(v_a_3968_);
    leanh::lean_dec_ref(v_a_3967_);
    leanh::lean_dec(v_a_3966_);
    leanh::lean_dec_ref(v_a_3965_);
    leanh::lean_dec_ref(v_a_3964_);
    return v_res_3970_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___boxed(
    mut v_as_3971_: *mut leanh::LeanObject,
    mut v_sz_3972_: *mut leanh::LeanObject,
    mut v_i_3973_: *mut leanh::LeanObject,
    mut v_b_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3981_: usize = 0;
    let mut v_i_boxed_3982_: usize = 0;
    let mut v_res_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3981_ = leanh::lean_unbox_usize(v_sz_3972_);
    leanh::lean_dec(v_sz_3972_);
    v_i_boxed_3982_ = leanh::lean_unbox_usize(v_i_3973_);
    leanh::lean_dec(v_i_3973_);
    v_res_3983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6(v_as_3971_, v_sz_boxed_3981_, v_i_boxed_3982_, v_b_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
    leanh::lean_dec(v___y_3979_);
    leanh::lean_dec_ref(v___y_3978_);
    leanh::lean_dec(v___y_3977_);
    leanh::lean_dec_ref(v___y_3976_);
    leanh::lean_dec_ref(v___y_3975_);
    leanh::lean_dec_ref(v_as_3971_);
    return v_res_3983_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___boxed(
    mut v_e_3984_: *mut leanh::LeanObject,
    mut v_a_3985_: *mut leanh::LeanObject,
    mut v_a_3986_: *mut leanh::LeanObject,
    mut v_a_3987_: *mut leanh::LeanObject,
    mut v_a_3988_: *mut leanh::LeanObject,
    mut v_a_3989_: *mut leanh::LeanObject,
    mut v_a_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3991_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(
        v_e_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_,
    );
    leanh::lean_dec(v_a_3989_);
    leanh::lean_dec_ref(v_a_3988_);
    leanh::lean_dec(v_a_3987_);
    leanh::lean_dec_ref(v_a_3986_);
    leanh::lean_dec_ref(v_a_3985_);
    return v_res_3991_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go___boxed(
    mut v_e_3992_: *mut leanh::LeanObject,
    mut v_fvars_3993_: *mut leanh::LeanObject,
    mut v_all_3994_: *mut leanh::LeanObject,
    mut v_a_3995_: *mut leanh::LeanObject,
    mut v_a_3996_: *mut leanh::LeanObject,
    mut v_a_3997_: *mut leanh::LeanObject,
    mut v_a_3998_: *mut leanh::LeanObject,
    mut v_a_3999_: *mut leanh::LeanObject,
    mut v_a_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4001_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go(v_e_3992_, v_fvars_3993_, v_all_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
    leanh::lean_dec(v_a_3999_);
    leanh::lean_dec_ref(v_a_3998_);
    leanh::lean_dec(v_a_3997_);
    leanh::lean_dec_ref(v_a_3996_);
    return v_res_4001_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go___boxed(
    mut v_e_4002_: *mut leanh::LeanObject,
    mut v_fvars_4003_: *mut leanh::LeanObject,
    mut v_a_4004_: *mut leanh::LeanObject,
    mut v_a_4005_: *mut leanh::LeanObject,
    mut v_a_4006_: *mut leanh::LeanObject,
    mut v_a_4007_: *mut leanh::LeanObject,
    mut v_a_4008_: *mut leanh::LeanObject,
    mut v_a_4009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4010_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go(v_e_4002_, v_fvars_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
    leanh::lean_dec(v_a_4008_);
    leanh::lean_dec_ref(v_a_4007_);
    leanh::lean_dec(v_a_4006_);
    leanh::lean_dec_ref(v_a_4005_);
    return v_res_4010_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(
    mut v___y_4011_: *mut leanh::LeanObject,
    mut v___y_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
    mut v___y_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___redArg(v___y_4015_);
    return v___x_4017_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3___boxed(
    mut v___y_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4024_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferLambdaType_go_spec__0_spec__3(v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
    leanh::lean_dec(v___y_4022_);
    leanh::lean_dec_ref(v___y_4021_);
    leanh::lean_dec(v___y_4020_);
    leanh::lean_dec_ref(v___y_4019_);
    leanh::lean_dec_ref(v___y_4018_);
    return v_res_4024_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(
    mut v_upperBound_4025_: *mut leanh::LeanObject,
    mut v___x_4026_: *mut leanh::LeanObject,
    mut v_inst_4027_: *mut leanh::LeanObject,
    mut v_R_4028_: *mut leanh::LeanObject,
    mut v_a_4029_: *mut leanh::LeanObject,
    mut v_b_4030_: *mut leanh::LeanObject,
    mut v_c_4031_: *mut leanh::LeanObject,
    mut v___y_4032_: *mut leanh::LeanObject,
    mut v___y_4033_: *mut leanh::LeanObject,
    mut v___y_4034_: *mut leanh::LeanObject,
    mut v___y_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4038_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg(v_upperBound_4025_, v___x_4026_, v_a_4029_, v_b_4030_);
    return v___x_4038_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___boxed(
    mut v_upperBound_4039_: *mut leanh::LeanObject,
    mut v___x_4040_: *mut leanh::LeanObject,
    mut v_inst_4041_: *mut leanh::LeanObject,
    mut v_R_4042_: *mut leanh::LeanObject,
    mut v_a_4043_: *mut leanh::LeanObject,
    mut v_b_4044_: *mut leanh::LeanObject,
    mut v_c_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4052_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9(v_upperBound_4039_, v___x_4040_, v_inst_4041_, v_R_4042_, v_a_4043_, v_b_4044_, v_c_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
    leanh::lean_dec(v___y_4050_);
    leanh::lean_dec_ref(v___y_4049_);
    leanh::lean_dec(v___y_4048_);
    leanh::lean_dec_ref(v___y_4047_);
    leanh::lean_dec_ref(v___y_4046_);
    leanh::lean_dec_ref(v___x_4040_);
    leanh::lean_dec(v_upperBound_4039_);
    return v_res_4052_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(
    mut v_arg_4053_: *mut leanh::LeanObject,
    mut v_a_4054_: *mut leanh::LeanObject,
    mut v_a_4055_: *mut leanh::LeanObject,
    mut v_a_4056_: *mut leanh::LeanObject,
    mut v_a_4057_: *mut leanh::LeanObject,
    mut v_a_4058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_arg_4053_) {
        0 => {
            let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4060_ = l_Lean_Compiler_LCNF_erasedExpr;
            v___x_4061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_4061_, 0, v___x_4060_);
            return v___x_4061_;
        }
        1 => {
            let mut v_fvarId_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_4062_ = leanh::lean_ctor_get(v_arg_4053_, 0);
            leanh::lean_inc(v_fvarId_4062_);
            leanh::lean_dec_ref_known(v_arg_4053_, 1);
            v___x_4063_ = l_Lean_Compiler_LCNF_getType(
                v_fvarId_4062_,
                v_a_4055_,
                v_a_4056_,
                v_a_4057_,
                v_a_4058_,
            );
            return v___x_4063_;
        }
        _ => {
            let mut v_expr_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_expr_4064_ = leanh::lean_ctor_get(v_arg_4053_, 0);
            leanh::lean_inc_ref(v_expr_4064_);
            leanh::lean_dec_ref_known(v_arg_4053_, 1);
            v___x_4065_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
                v_expr_4064_,
                v_a_4054_,
                v_a_4055_,
                v_a_4056_,
                v_a_4057_,
                v_a_4058_,
            );
            return v___x_4065_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferArgType___boxed(
    mut v_arg_4066_: *mut leanh::LeanObject,
    mut v_a_4067_: *mut leanh::LeanObject,
    mut v_a_4068_: *mut leanh::LeanObject,
    mut v_a_4069_: *mut leanh::LeanObject,
    mut v_a_4070_: *mut leanh::LeanObject,
    mut v_a_4071_: *mut leanh::LeanObject,
    mut v_a_4072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(
        v_arg_4066_,
        v_a_4067_,
        v_a_4068_,
        v_a_4069_,
        v_a_4070_,
        v_a_4071_,
    );
    leanh::lean_dec(v_a_4071_);
    leanh::lean_dec_ref(v_a_4070_);
    leanh::lean_dec(v_a_4069_);
    leanh::lean_dec_ref(v_a_4068_);
    leanh::lean_dec_ref(v_a_4067_);
    return v_res_4073_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(
    mut v_upperBound_4074_: *mut leanh::LeanObject,
    mut v_args_4075_: *mut leanh::LeanObject,
    mut v_a_4076_: *mut leanh::LeanObject,
    mut v_b_4077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4089_: u8 = 0;
    let mut v_fst_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4094_: u8 = 0;
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4121_: u8 = 0;
    let mut v_isSharedCheck_4122_: u8 = 0;
    let mut v_unused_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4084_ = lean_nat_dec_lt(v_a_4076_, v_upperBound_4074_);
                if v___x_4084_ == 0 {
                    leanh::lean_dec(v_a_4076_);
                    leanh::lean_dec_ref(v_args_4075_);
                    v___x_4085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4085_, 0, v_b_4077_);
                    return v___x_4085_;
                } else {
                    v_snd_4086_ = leanh::lean_ctor_get(v_b_4077_, 1);
                    v_isSharedCheck_4122_ = (!leanh::lean_is_exclusive(v_b_4077_)) as u8;
                    if v_isSharedCheck_4122_ == 0 {
                        v_unused_4123_ = leanh::lean_ctor_get(v_b_4077_, 0);
                        leanh::lean_dec(v_unused_4123_);
                        v___x_4088_ = v_b_4077_;
                        v_isShared_4089_ = v_isSharedCheck_4122_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4086_);
                        leanh::lean_dec(v_b_4077_);
                        v___x_4088_ = leanh::lean_box(0);
                        v_isShared_4089_ = v_isSharedCheck_4122_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4081_ = leanh::lean_unsigned_to_nat(1);
                v___x_4082_ = lean_nat_add(v_a_4076_, v___x_4081_);
                leanh::lean_dec(v_a_4076_);
                v_a_4076_ = v___x_4082_;
                v_b_4077_ = v_a_4080_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_4090_ = leanh::lean_ctor_get(v_snd_4086_, 0);
                v_snd_4091_ = leanh::lean_ctor_get(v_snd_4086_, 1);
                v_isSharedCheck_4121_ = (!leanh::lean_is_exclusive(v_snd_4086_)) as u8;
                if v_isSharedCheck_4121_ == 0 {
                    v___x_4093_ = v_snd_4086_;
                    v_isShared_4094_ = v_isSharedCheck_4121_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4091_);
                    leanh::lean_inc(v_fst_4090_);
                    leanh::lean_dec(v_snd_4086_);
                    v___x_4093_ = leanh::lean_box(0);
                    v_isShared_4094_ = v_isSharedCheck_4121_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4095_ = leanh::lean_box(0);
                v___x_4096_ = l_Lean_Expr_headBeta(v_snd_4091_);
                if leanh::lean_obj_tag(v___x_4096_) == 7 {
                    v_body_4097_ = leanh::lean_ctor_get(v___x_4096_, 2);
                    leanh::lean_inc_ref(v_body_4097_);
                    leanh::lean_dec_ref_known(v___x_4096_, 3);
                    if v_isShared_4094_ == 0 {
                        leanh::lean_ctor_set(v___x_4093_, 1, v_body_4097_);
                        v___x_4099_ = v___x_4093_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4103_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_fst_4090_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 1, v_body_4097_);
                        v___x_4099_ = v_reuseFailAlloc_4103_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_args_4075_);
                    v___x_4104_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                        v___x_4096_,
                        v_fst_4090_,
                        v_a_4076_,
                        v_args_4075_,
                    );
                    leanh::lean_dec_ref(v___x_4096_);
                    v___x_4105_ = l_Lean_Expr_headBeta(v___x_4104_);
                    if leanh::lean_obj_tag(v___x_4105_) == 7 {
                        leanh::lean_dec(v_fst_4090_);
                        v_body_4106_ = leanh::lean_ctor_get(v___x_4105_, 2);
                        leanh::lean_inc_ref(v_body_4106_);
                        leanh::lean_dec_ref_known(v___x_4105_, 3);
                        leanh::lean_inc(v_a_4076_);
                        if v_isShared_4094_ == 0 {
                            leanh::lean_ctor_set(v___x_4093_, 1, v_body_4106_);
                            leanh::lean_ctor_set(v___x_4093_, 0, v_a_4076_);
                            v___x_4108_ = v___x_4093_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4112_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4076_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_body_4106_);
                            v___x_4108_ = v_reuseFailAlloc_4112_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4076_);
                        leanh::lean_dec_ref(v_args_4075_);
                        v___x_4113_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppType_spec__9___redArg___closed__0);
                        if v_isShared_4094_ == 0 {
                            leanh::lean_ctor_set(v___x_4093_, 1, v___x_4105_);
                            v___x_4115_ = v___x_4093_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4120_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_fst_4090_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4105_);
                            v___x_4115_ = v_reuseFailAlloc_4120_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_4089_ == 0 {
                    leanh::lean_ctor_set(v___x_4088_, 1, v___x_4099_);
                    leanh::lean_ctor_set(v___x_4088_, 0, v___x_4095_);
                    v___x_4101_ = v___x_4088_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4102_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4102_, 1, v___x_4099_);
                    v___x_4101_ = v_reuseFailAlloc_4102_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_4080_ = v___x_4101_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_4089_ == 0 {
                    leanh::lean_ctor_set(v___x_4088_, 1, v___x_4108_);
                    leanh::lean_ctor_set(v___x_4088_, 0, v___x_4095_);
                    v___x_4110_ = v___x_4088_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4111_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 1, v___x_4108_);
                    v___x_4110_ = v_reuseFailAlloc_4111_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_4080_ = v___x_4110_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_4089_ == 0 {
                    leanh::lean_ctor_set(v___x_4088_, 1, v___x_4115_);
                    leanh::lean_ctor_set(v___x_4088_, 0, v___x_4113_);
                    v___x_4117_ = v___x_4088_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4113_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4115_);
                    v___x_4117_ = v_reuseFailAlloc_4119_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4118_, 0, v___x_4117_);
                return v___x_4118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg___boxed(
    mut v_upperBound_4124_: *mut leanh::LeanObject,
    mut v_args_4125_: *mut leanh::LeanObject,
    mut v_a_4126_: *mut leanh::LeanObject,
    mut v_b_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_4124_, v_args_4125_, v_a_4126_, v_b_4127_);
    leanh::lean_dec(v_upperBound_4124_);
    return v_res_4129_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(
    mut v_fType_4130_: *mut leanh::LeanObject,
    mut v_args_4131_: *mut leanh::LeanObject,
    mut v_a_4132_: *mut leanh::LeanObject,
    mut v_a_4133_: *mut leanh::LeanObject,
    mut v_a_4134_: *mut leanh::LeanObject,
    mut v_a_4135_: *mut leanh::LeanObject,
    mut v_a_4136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4147_: u8 = 0;
    let mut v_fst_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4161_: u8 = 0;
    let mut v_a_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4138_ = lean_array_get_size(v_args_4131_);
                v___x_4139_ = leanh::lean_unsigned_to_nat(0);
                v___x_4140_ = leanh::lean_box(0);
                v___x_4141_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4141_, 0, v___x_4139_);
                leanh::lean_ctor_set(v___x_4141_, 1, v_fType_4130_);
                v___x_4142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4142_, 0, v___x_4140_);
                leanh::lean_ctor_set(v___x_4142_, 1, v___x_4141_);
                leanh::lean_inc_ref(v_args_4131_);
                v___x_4143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v___x_4138_, v_args_4131_, v___x_4139_, v___x_4142_);
                if leanh::lean_obj_tag(v___x_4143_) == 0 {
                    v_a_4144_ = leanh::lean_ctor_get(v___x_4143_, 0);
                    v_isSharedCheck_4161_ = (!leanh::lean_is_exclusive(v___x_4143_)) as u8;
                    if v_isSharedCheck_4161_ == 0 {
                        v___x_4146_ = v___x_4143_;
                        v_isShared_4147_ = v_isSharedCheck_4161_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4144_);
                        leanh::lean_dec(v___x_4143_);
                        v___x_4146_ = leanh::lean_box(0);
                        v_isShared_4147_ = v_isSharedCheck_4161_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_args_4131_);
                    v_a_4162_ = leanh::lean_ctor_get(v___x_4143_, 0);
                    v_isSharedCheck_4169_ = (!leanh::lean_is_exclusive(v___x_4143_)) as u8;
                    if v_isSharedCheck_4169_ == 0 {
                        v___x_4164_ = v___x_4143_;
                        v_isShared_4165_ = v_isSharedCheck_4169_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4162_);
                        leanh::lean_dec(v___x_4143_);
                        v___x_4164_ = leanh::lean_box(0);
                        v_isShared_4165_ = v_isSharedCheck_4169_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4148_ = leanh::lean_ctor_get(v_a_4144_, 0);
                if leanh::lean_obj_tag(v_fst_4148_) == 0 {
                    v_snd_4149_ = leanh::lean_ctor_get(v_a_4144_, 1);
                    leanh::lean_inc(v_snd_4149_);
                    leanh::lean_dec(v_a_4144_);
                    v_fst_4150_ = leanh::lean_ctor_get(v_snd_4149_, 0);
                    leanh::lean_inc(v_fst_4150_);
                    v_snd_4151_ = leanh::lean_ctor_get(v_snd_4149_, 1);
                    leanh::lean_inc(v_snd_4151_);
                    leanh::lean_dec(v_snd_4149_);
                    v___x_4152_ = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(
                        v_snd_4151_,
                        v_fst_4150_,
                        v___x_4138_,
                        v_args_4131_,
                    );
                    leanh::lean_dec(v_fst_4150_);
                    leanh::lean_dec(v_snd_4151_);
                    v___x_4153_ = l_Lean_Expr_headBeta(v___x_4152_);
                    if v_isShared_4147_ == 0 {
                        leanh::lean_ctor_set(v___x_4146_, 0, v___x_4153_);
                        v___x_4155_ = v___x_4146_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
                        v___x_4155_ = v_reuseFailAlloc_4156_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4148_);
                    leanh::lean_dec(v_a_4144_);
                    leanh::lean_dec_ref(v_args_4131_);
                    v_val_4157_ = leanh::lean_ctor_get(v_fst_4148_, 0);
                    leanh::lean_inc(v_val_4157_);
                    leanh::lean_dec_ref_known(v_fst_4148_, 1);
                    if v_isShared_4147_ == 0 {
                        leanh::lean_ctor_set(v___x_4146_, 0, v_val_4157_);
                        v___x_4159_ = v___x_4146_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4160_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_val_4157_);
                        v___x_4159_ = v_reuseFailAlloc_4160_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4155_;
            }
            3 => {
                return v___x_4159_;
            }
            4 => {
                if v_isShared_4165_ == 0 {
                    v___x_4167_ = v___x_4164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
                    v___x_4167_ = v_reuseFailAlloc_4168_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore___boxed(
    mut v_fType_4170_: *mut leanh::LeanObject,
    mut v_args_4171_: *mut leanh::LeanObject,
    mut v_a_4172_: *mut leanh::LeanObject,
    mut v_a_4173_: *mut leanh::LeanObject,
    mut v_a_4174_: *mut leanh::LeanObject,
    mut v_a_4175_: *mut leanh::LeanObject,
    mut v_a_4176_: *mut leanh::LeanObject,
    mut v_a_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4178_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(
        v_fType_4170_,
        v_args_4171_,
        v_a_4172_,
        v_a_4173_,
        v_a_4174_,
        v_a_4175_,
        v_a_4176_,
    );
    leanh::lean_dec(v_a_4176_);
    leanh::lean_dec_ref(v_a_4175_);
    leanh::lean_dec(v_a_4174_);
    leanh::lean_dec_ref(v_a_4173_);
    leanh::lean_dec_ref(v_a_4172_);
    return v_res_4178_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(
    mut v_upperBound_4179_: *mut leanh::LeanObject,
    mut v_args_4180_: *mut leanh::LeanObject,
    mut v_inst_4181_: *mut leanh::LeanObject,
    mut v_R_4182_: *mut leanh::LeanObject,
    mut v_a_4183_: *mut leanh::LeanObject,
    mut v_b_4184_: *mut leanh::LeanObject,
    mut v_c_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___redArg(v_upperBound_4179_, v_args_4180_, v_a_4183_, v_b_4184_);
    return v___x_4192_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0___boxed(
    mut v_upperBound_4193_: *mut leanh::LeanObject,
    mut v_args_4194_: *mut leanh::LeanObject,
    mut v_inst_4195_: *mut leanh::LeanObject,
    mut v_R_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_b_4198_: *mut leanh::LeanObject,
    mut v_c_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore_spec__0(v_upperBound_4193_, v_args_4194_, v_inst_4195_, v_R_4196_, v_a_4197_, v_b_4198_, v_c_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    leanh::lean_dec(v___y_4204_);
    leanh::lean_dec_ref(v___y_4203_);
    leanh::lean_dec(v___y_4202_);
    leanh::lean_dec_ref(v___y_4201_);
    leanh::lean_dec_ref(v___y_4200_);
    leanh::lean_dec(v_upperBound_4193_);
    return v_res_4206_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4207_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__0);
    v___x_4209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
    return v___x_4209_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
    v___x_4211_ = leanh::lean_unsigned_to_nat(0);
    v___x_4212_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4212_, 0, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 2, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 3, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 4, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 5, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 6, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 7, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 8, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 9, v___x_4210_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(
    mut v_msg_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
    mut v___y_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4227_: u8 = 0;
    let mut v_env_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4233_: u8 = 0;
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v_unused_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v_a_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4219_ = leanh::lean_ctor_get(v___y_4216_, 2);
                v_ref_4220_ = leanh::lean_ctor_get(v___y_4216_, 5);
                v___x_4221_ = lean_st_ref_get(v___y_4217_);
                v___x_4222_ = lean_st_ref_get(v___y_4215_);
                v___x_4223_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4214_);
                if leanh::lean_obj_tag(v___x_4223_) == 0 {
                    v_a_4224_ = leanh::lean_ctor_get(v___x_4223_, 0);
                    v_isSharedCheck_4246_ = (!leanh::lean_is_exclusive(v___x_4223_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4226_ = v___x_4223_;
                        v_isShared_4227_ = v_isSharedCheck_4246_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4224_);
                        leanh::lean_dec(v___x_4223_);
                        v___x_4226_ = leanh::lean_box(0);
                        v_isShared_4227_ = v_isSharedCheck_4246_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4222_);
                    leanh::lean_dec(v___x_4221_);
                    leanh::lean_dec_ref(v_msg_4213_);
                    v_a_4247_ = leanh::lean_ctor_get(v___x_4223_, 0);
                    v_isSharedCheck_4254_ = (!leanh::lean_is_exclusive(v___x_4223_)) as u8;
                    if v_isSharedCheck_4254_ == 0 {
                        v___x_4249_ = v___x_4223_;
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4247_);
                        leanh::lean_dec(v___x_4223_);
                        v___x_4249_ = leanh::lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4254_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_4228_ = leanh::lean_ctor_get(v___x_4221_, 0);
                leanh::lean_inc_ref(v_env_4228_);
                leanh::lean_dec(v___x_4221_);
                v_lctx_4229_ = leanh::lean_ctor_get(v___x_4222_, 0);
                v_isSharedCheck_4244_ = (!leanh::lean_is_exclusive(v___x_4222_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v_unused_4245_ = leanh::lean_ctor_get(v___x_4222_, 1);
                    leanh::lean_dec(v_unused_4245_);
                    v___x_4231_ = v___x_4222_;
                    v_isShared_4232_ = v_isSharedCheck_4244_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_4229_);
                    leanh::lean_dec(v___x_4222_);
                    v___x_4231_ = leanh::lean_box(0);
                    v_isShared_4232_ = v_isSharedCheck_4244_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4233_ = (leanh::lean_unbox(v_a_4224_) as u8);
                leanh::lean_dec(v_a_4224_);
                v___x_4234_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4229_, v___x_4233_);
                leanh::lean_dec_ref(v_lctx_4229_);
                v___x_4235_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
                leanh::lean_inc_ref(v_options_4219_);
                v___x_4236_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4236_, 0, v_env_4228_);
                leanh::lean_ctor_set(v___x_4236_, 1, v___x_4235_);
                leanh::lean_ctor_set(v___x_4236_, 2, v___x_4234_);
                leanh::lean_ctor_set(v___x_4236_, 3, v_options_4219_);
                if v_isShared_4232_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4231_, 3);
                    leanh::lean_ctor_set(v___x_4231_, 1, v_msg_4213_);
                    leanh::lean_ctor_set(v___x_4231_, 0, v___x_4236_);
                    v___x_4238_ = v___x_4231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_msg_4213_);
                    v___x_4238_ = v_reuseFailAlloc_4243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ref_4220_);
                v___x_4239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4239_, 0, v_ref_4220_);
                leanh::lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                if v_isShared_4227_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4226_, 1);
                    leanh::lean_ctor_set(v___x_4226_, 0, v___x_4239_);
                    v___x_4241_ = v___x_4226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
                    v___x_4241_ = v_reuseFailAlloc_4242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4241_;
            }
            5 => {
                if v_isShared_4250_ == 0 {
                    v___x_4252_ = v___x_4249_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4253_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
                    v___x_4252_ = v_reuseFailAlloc_4253_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___boxed(
    mut v_msg_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4261_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(
            v_msg_4255_,
            v___y_4256_,
            v___y_4257_,
            v___y_4258_,
            v___y_4259_,
        );
    leanh::lean_dec(v___y_4259_);
    leanh::lean_dec_ref(v___y_4258_);
    leanh::lean_dec(v___y_4257_);
    leanh::lean_dec_ref(v___y_4256_);
    return v_res_4261_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(
    mut v_00_u03b1_4262_: *mut leanh::LeanObject,
    mut v_msg_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
    mut v___y_4266_: *mut leanh::LeanObject,
    mut v___y_4267_: *mut leanh::LeanObject,
    mut v___y_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4270_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(
            v_msg_4263_,
            v___y_4265_,
            v___y_4266_,
            v___y_4267_,
            v___y_4268_,
        );
    return v___x_4270_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___boxed(
    mut v_00_u03b1_4271_: *mut leanh::LeanObject,
    mut v_msg_4272_: *mut leanh::LeanObject,
    mut v___y_4273_: *mut leanh::LeanObject,
    mut v___y_4274_: *mut leanh::LeanObject,
    mut v___y_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
    mut v___y_4278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0(
            v_00_u03b1_4271_,
            v_msg_4272_,
            v___y_4273_,
            v___y_4274_,
            v___y_4275_,
            v___y_4276_,
            v___y_4277_,
        );
    leanh::lean_dec(v___y_4277_);
    leanh::lean_dec_ref(v___y_4276_);
    leanh::lean_dec(v___y_4275_);
    leanh::lean_dec_ref(v___y_4274_);
    leanh::lean_dec_ref(v___y_4273_);
    return v_res_4279_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__0;
    v___x_4282_ = l_Lean_stringToMessageData(v___x_4281_);
    return v___x_4282_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(
    mut v_upperBound_4283_: *mut leanh::LeanObject,
    mut v_s_4284_: *mut leanh::LeanObject,
    mut v_structName_4285_: *mut leanh::LeanObject,
    mut v_idx_4286_: *mut leanh::LeanObject,
    mut v_a_4287_: *mut leanh::LeanObject,
    mut v_b_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
    mut v___y_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4330_: u8 = 0;
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4334_: u8 = 0;
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v_unused_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4300_ = lean_nat_dec_lt(v_a_4287_, v_upperBound_4283_);
                if v___x_4300_ == 0 {
                    leanh::lean_dec(v_a_4287_);
                    leanh::lean_dec(v_idx_4286_);
                    leanh::lean_dec(v_structName_4285_);
                    leanh::lean_dec(v_s_4284_);
                    v___x_4301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4301_, 0, v_b_4288_);
                    return v___x_4301_;
                } else {
                    v_snd_4302_ = leanh::lean_ctor_get(v_b_4288_, 1);
                    v_isSharedCheck_4340_ = (!leanh::lean_is_exclusive(v_b_4288_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v_unused_4341_ = leanh::lean_ctor_get(v_b_4288_, 0);
                        leanh::lean_dec(v_unused_4341_);
                        v___x_4304_ = v_b_4288_;
                        v_isShared_4305_ = v_isSharedCheck_4340_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4302_);
                        leanh::lean_dec(v_b_4288_);
                        v___x_4304_ = leanh::lean_box(0);
                        v_isShared_4305_ = v_isSharedCheck_4340_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4297_ = leanh::lean_unsigned_to_nat(1);
                v___x_4298_ = lean_nat_add(v_a_4287_, v___x_4297_);
                leanh::lean_dec(v_a_4287_);
                v_a_4287_ = v___x_4298_;
                v_b_4288_ = v_a_4296_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4306_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_snd_4302_) == 7 {
                    v_body_4307_ = leanh::lean_ctor_get(v_snd_4302_, 2);
                    leanh::lean_inc_ref(v_body_4307_);
                    leanh::lean_dec_ref_known(v_snd_4302_, 3);
                    v___x_4308_ = l_Lean_Expr_hasLooseBVars(v_body_4307_);
                    if v___x_4308_ == 0 {
                        if v_isShared_4305_ == 0 {
                            leanh::lean_ctor_set(v___x_4304_, 1, v_body_4307_);
                            leanh::lean_ctor_set(v___x_4304_, 0, v___x_4306_);
                            v___x_4310_ = v___x_4304_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4311_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 0, v___x_4306_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4311_, 1, v_body_4307_);
                            v___x_4310_ = v_reuseFailAlloc_4311_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4312_ = l_Lean_Compiler_LCNF_anyExpr;
                        v___x_4313_ = lean_expr_instantiate1(v_body_4307_, v___x_4312_);
                        leanh::lean_dec_ref(v_body_4307_);
                        if v_isShared_4305_ == 0 {
                            leanh::lean_ctor_set(v___x_4304_, 1, v___x_4313_);
                            leanh::lean_ctor_set(v___x_4304_, 0, v___x_4306_);
                            v___x_4315_ = v___x_4304_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4316_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4306_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 1, v___x_4313_);
                            v___x_4315_ = v_reuseFailAlloc_4316_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_4317_ = l_Lean_Expr_isErased(v_snd_4302_);
                    if v___x_4317_ == 0 {
                        v___x_4318_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
                        leanh::lean_inc(v_s_4284_);
                        v___x_4319_ = l_Lean_mkFVar(v_s_4284_);
                        leanh::lean_inc(v_idx_4286_);
                        leanh::lean_inc(v_structName_4285_);
                        v___x_4320_ = l_Lean_mkProj(v_structName_4285_, v_idx_4286_, v___x_4319_);
                        v___x_4321_ = l_Lean_indentExpr(v___x_4320_);
                        v___x_4322_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4322_, 0, v___x_4318_);
                        leanh::lean_ctor_set(v___x_4322_, 1, v___x_4321_);
                        v___x_4323_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_4322_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
                        if leanh::lean_obj_tag(v___x_4323_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4323_, 1);
                            if v_isShared_4305_ == 0 {
                                leanh::lean_ctor_set(v___x_4304_, 0, v___x_4306_);
                                v___x_4325_ = v___x_4304_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_4326_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4306_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4326_, 1, v_snd_4302_);
                                v___x_4325_ = v_reuseFailAlloc_4326_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_4304_);
                            leanh::lean_dec(v_snd_4302_);
                            leanh::lean_dec(v_a_4287_);
                            leanh::lean_dec(v_idx_4286_);
                            leanh::lean_dec(v_structName_4285_);
                            leanh::lean_dec(v_s_4284_);
                            v_a_4327_ = leanh::lean_ctor_get(v___x_4323_, 0);
                            v_isSharedCheck_4334_ =
                                (!leanh::lean_is_exclusive(v___x_4323_)) as u8;
                            if v_isSharedCheck_4334_ == 0 {
                                v___x_4329_ = v___x_4323_;
                                v_isShared_4330_ = v_isSharedCheck_4334_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4327_);
                                leanh::lean_dec(v___x_4323_);
                                v___x_4329_ = leanh::lean_box(0);
                                v_isShared_4330_ = v_isSharedCheck_4334_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4287_);
                        leanh::lean_dec(v_idx_4286_);
                        leanh::lean_dec(v_structName_4285_);
                        leanh::lean_dec(v_s_4284_);
                        v___x_4335_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
                        if v_isShared_4305_ == 0 {
                            leanh::lean_ctor_set(v___x_4304_, 0, v___x_4335_);
                            v___x_4337_ = v___x_4304_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4339_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4335_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_snd_4302_);
                            v___x_4337_ = v_reuseFailAlloc_4339_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_4296_ = v___x_4310_;
                state = 1;
                continue;
            }
            4 => {
                v_a_4296_ = v___x_4315_;
                state = 1;
                continue;
            }
            5 => {
                v_a_4296_ = v___x_4325_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_4330_ == 0 {
                    v___x_4332_ = v___x_4329_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4333_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
                    v___x_4332_ = v_reuseFailAlloc_4333_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4332_;
            }
            8 => {
                v___x_4338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4338_, 0, v___x_4337_);
                return v___x_4338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___boxed(
    mut v_upperBound_4342_: *mut leanh::LeanObject,
    mut v_s_4343_: *mut leanh::LeanObject,
    mut v_structName_4344_: *mut leanh::LeanObject,
    mut v_idx_4345_: *mut leanh::LeanObject,
    mut v_a_4346_: *mut leanh::LeanObject,
    mut v_b_4347_: *mut leanh::LeanObject,
    mut v___y_4348_: *mut leanh::LeanObject,
    mut v___y_4349_: *mut leanh::LeanObject,
    mut v___y_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
    mut v___y_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4354_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_4342_, v_s_4343_, v_structName_4344_, v_idx_4345_, v_a_4346_, v_b_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
    leanh::lean_dec(v___y_4352_);
    leanh::lean_dec_ref(v___y_4351_);
    leanh::lean_dec(v___y_4350_);
    leanh::lean_dec_ref(v___y_4349_);
    leanh::lean_dec_ref(v___y_4348_);
    leanh::lean_dec(v_upperBound_4342_);
    return v_res_4354_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(
    mut v_upperBound_4355_: *mut leanh::LeanObject,
    mut v_s_4356_: *mut leanh::LeanObject,
    mut v_structName_4357_: *mut leanh::LeanObject,
    mut v_idx_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
    mut v_b_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
    mut v___y_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: u8 = 0;
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_unused_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4372_ = lean_nat_dec_lt(v_a_4359_, v_upperBound_4355_);
                if v___x_4372_ == 0 {
                    leanh::lean_dec(v_idx_4358_);
                    leanh::lean_dec(v_structName_4357_);
                    leanh::lean_dec(v_s_4356_);
                    v___x_4373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4373_, 0, v_b_4360_);
                    return v___x_4373_;
                } else {
                    v_snd_4374_ = leanh::lean_ctor_get(v_b_4360_, 1);
                    v_isSharedCheck_4412_ = (!leanh::lean_is_exclusive(v_b_4360_)) as u8;
                    if v_isSharedCheck_4412_ == 0 {
                        v_unused_4413_ = leanh::lean_ctor_get(v_b_4360_, 0);
                        leanh::lean_dec(v_unused_4413_);
                        v___x_4376_ = v_b_4360_;
                        v_isShared_4377_ = v_isSharedCheck_4412_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4374_);
                        leanh::lean_dec(v_b_4360_);
                        v___x_4376_ = leanh::lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4412_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4369_ = leanh::lean_unsigned_to_nat(1);
                v___x_4370_ = lean_nat_add(v_a_4359_, v___x_4369_);
                v___x_4371_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_4355_, v_s_4356_, v_structName_4357_, v_idx_4358_, v___x_4370_, v_a_4368_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
                return v___x_4371_;
            }
            2 => {
                v___x_4378_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_snd_4374_) == 7 {
                    v_body_4379_ = leanh::lean_ctor_get(v_snd_4374_, 2);
                    leanh::lean_inc_ref(v_body_4379_);
                    leanh::lean_dec_ref_known(v_snd_4374_, 3);
                    v___x_4380_ = l_Lean_Expr_hasLooseBVars(v_body_4379_);
                    if v___x_4380_ == 0 {
                        if v_isShared_4377_ == 0 {
                            leanh::lean_ctor_set(v___x_4376_, 1, v_body_4379_);
                            leanh::lean_ctor_set(v___x_4376_, 0, v___x_4378_);
                            v___x_4382_ = v___x_4376_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4383_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4378_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 1, v_body_4379_);
                            v___x_4382_ = v_reuseFailAlloc_4383_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4384_ = l_Lean_Compiler_LCNF_anyExpr;
                        v___x_4385_ = lean_expr_instantiate1(v_body_4379_, v___x_4384_);
                        leanh::lean_dec_ref(v_body_4379_);
                        if v_isShared_4377_ == 0 {
                            leanh::lean_ctor_set(v___x_4376_, 1, v___x_4385_);
                            leanh::lean_ctor_set(v___x_4376_, 0, v___x_4378_);
                            v___x_4387_ = v___x_4376_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4388_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4378_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 1, v___x_4385_);
                            v___x_4387_ = v_reuseFailAlloc_4388_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_4389_ = l_Lean_Expr_isErased(v_snd_4374_);
                    if v___x_4389_ == 0 {
                        v___x_4390_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
                        leanh::lean_inc(v_s_4356_);
                        v___x_4391_ = l_Lean_mkFVar(v_s_4356_);
                        leanh::lean_inc(v_idx_4358_);
                        leanh::lean_inc(v_structName_4357_);
                        v___x_4392_ = l_Lean_mkProj(v_structName_4357_, v_idx_4358_, v___x_4391_);
                        v___x_4393_ = l_Lean_indentExpr(v___x_4392_);
                        v___x_4394_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4394_, 0, v___x_4390_);
                        leanh::lean_ctor_set(v___x_4394_, 1, v___x_4393_);
                        v___x_4395_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_4394_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
                        if leanh::lean_obj_tag(v___x_4395_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4395_, 1);
                            if v_isShared_4377_ == 0 {
                                leanh::lean_ctor_set(v___x_4376_, 0, v___x_4378_);
                                v___x_4397_ = v___x_4376_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_4398_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4378_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 1, v_snd_4374_);
                                v___x_4397_ = v_reuseFailAlloc_4398_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_4376_);
                            leanh::lean_dec(v_snd_4374_);
                            leanh::lean_dec(v_idx_4358_);
                            leanh::lean_dec(v_structName_4357_);
                            leanh::lean_dec(v_s_4356_);
                            v_a_4399_ = leanh::lean_ctor_get(v___x_4395_, 0);
                            v_isSharedCheck_4406_ =
                                (!leanh::lean_is_exclusive(v___x_4395_)) as u8;
                            if v_isSharedCheck_4406_ == 0 {
                                v___x_4401_ = v___x_4395_;
                                v_isShared_4402_ = v_isSharedCheck_4406_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4399_);
                                leanh::lean_dec(v___x_4395_);
                                v___x_4401_ = leanh::lean_box(0);
                                v_isShared_4402_ = v_isSharedCheck_4406_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_idx_4358_);
                        leanh::lean_dec(v_structName_4357_);
                        leanh::lean_dec(v_s_4356_);
                        v___x_4407_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_InferType_Pure_inferForallType_go_spec__6___closed__0);
                        if v_isShared_4377_ == 0 {
                            leanh::lean_ctor_set(v___x_4376_, 0, v___x_4407_);
                            v___x_4409_ = v___x_4376_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4411_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4407_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_snd_4374_);
                            v___x_4409_ = v_reuseFailAlloc_4411_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_a_4368_ = v___x_4382_;
                state = 1;
                continue;
            }
            4 => {
                v_a_4368_ = v___x_4387_;
                state = 1;
                continue;
            }
            5 => {
                v_a_4368_ = v___x_4397_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4404_;
            }
            8 => {
                v___x_4410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4410_, 0, v___x_4409_);
                return v___x_4410_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg___boxed(
    mut v_upperBound_4414_: *mut leanh::LeanObject,
    mut v_s_4415_: *mut leanh::LeanObject,
    mut v_structName_4416_: *mut leanh::LeanObject,
    mut v_idx_4417_: *mut leanh::LeanObject,
    mut v_a_4418_: *mut leanh::LeanObject,
    mut v_b_4419_: *mut leanh::LeanObject,
    mut v___y_4420_: *mut leanh::LeanObject,
    mut v___y_4421_: *mut leanh::LeanObject,
    mut v___y_4422_: *mut leanh::LeanObject,
    mut v___y_4423_: *mut leanh::LeanObject,
    mut v___y_4424_: *mut leanh::LeanObject,
    mut v___y_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_4414_, v_s_4415_, v_structName_4416_, v_idx_4417_, v_a_4418_, v_b_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
    leanh::lean_dec(v___y_4424_);
    leanh::lean_dec_ref(v___y_4423_);
    leanh::lean_dec(v___y_4422_);
    leanh::lean_dec_ref(v___y_4421_);
    leanh::lean_dec_ref(v___y_4420_);
    leanh::lean_dec(v_a_4418_);
    leanh::lean_dec(v_upperBound_4414_);
    return v_res_4426_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_ref_4427_: *mut leanh::LeanObject,
    mut v_msg_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4447_: u8 = 0;
    let mut v_cancelTk_x3f_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4449_: u8 = 0;
    let mut v_inheritedTraceOptions_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4435_ = leanh::lean_ctor_get(v___y_4432_, 0);
    v_fileMap_4436_ = leanh::lean_ctor_get(v___y_4432_, 1);
    v_options_4437_ = leanh::lean_ctor_get(v___y_4432_, 2);
    v_currRecDepth_4438_ = leanh::lean_ctor_get(v___y_4432_, 3);
    v_maxRecDepth_4439_ = leanh::lean_ctor_get(v___y_4432_, 4);
    v_ref_4440_ = leanh::lean_ctor_get(v___y_4432_, 5);
    v_currNamespace_4441_ = leanh::lean_ctor_get(v___y_4432_, 6);
    v_openDecls_4442_ = leanh::lean_ctor_get(v___y_4432_, 7);
    v_initHeartbeats_4443_ = leanh::lean_ctor_get(v___y_4432_, 8);
    v_maxHeartbeats_4444_ = leanh::lean_ctor_get(v___y_4432_, 9);
    v_quotContext_4445_ = leanh::lean_ctor_get(v___y_4432_, 10);
    v_currMacroScope_4446_ = leanh::lean_ctor_get(v___y_4432_, 11);
    v_diag_4447_ = leanh::lean_ctor_get_uint8(
        v___y_4432_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4448_ = leanh::lean_ctor_get(v___y_4432_, 12);
    v_suppressElabErrors_4449_ = leanh::lean_ctor_get_uint8(
        v___y_4432_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4450_ = leanh::lean_ctor_get(v___y_4432_, 13);
    v_ref_4451_ = l_Lean_replaceRef(v_ref_4427_, v_ref_4440_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_4450_);
    leanh::lean_inc(v_cancelTk_x3f_4448_);
    leanh::lean_inc(v_currMacroScope_4446_);
    leanh::lean_inc(v_quotContext_4445_);
    leanh::lean_inc(v_maxHeartbeats_4444_);
    leanh::lean_inc(v_initHeartbeats_4443_);
    leanh::lean_inc(v_openDecls_4442_);
    leanh::lean_inc(v_currNamespace_4441_);
    leanh::lean_inc(v_maxRecDepth_4439_);
    leanh::lean_inc(v_currRecDepth_4438_);
    leanh::lean_inc_ref(v_options_4437_);
    leanh::lean_inc_ref(v_fileMap_4436_);
    leanh::lean_inc_ref(v_fileName_4435_);
    v___x_4452_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_4452_, 0, v_fileName_4435_);
    leanh::lean_ctor_set(v___x_4452_, 1, v_fileMap_4436_);
    leanh::lean_ctor_set(v___x_4452_, 2, v_options_4437_);
    leanh::lean_ctor_set(v___x_4452_, 3, v_currRecDepth_4438_);
    leanh::lean_ctor_set(v___x_4452_, 4, v_maxRecDepth_4439_);
    leanh::lean_ctor_set(v___x_4452_, 5, v_ref_4451_);
    leanh::lean_ctor_set(v___x_4452_, 6, v_currNamespace_4441_);
    leanh::lean_ctor_set(v___x_4452_, 7, v_openDecls_4442_);
    leanh::lean_ctor_set(v___x_4452_, 8, v_initHeartbeats_4443_);
    leanh::lean_ctor_set(v___x_4452_, 9, v_maxHeartbeats_4444_);
    leanh::lean_ctor_set(v___x_4452_, 10, v_quotContext_4445_);
    leanh::lean_ctor_set(v___x_4452_, 11, v_currMacroScope_4446_);
    leanh::lean_ctor_set(v___x_4452_, 12, v_cancelTk_x3f_4448_);
    leanh::lean_ctor_set(v___x_4452_, 13, v_inheritedTraceOptions_4450_);
    leanh::lean_ctor_set_uint8(
        v___x_4452_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_4447_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4452_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4449_,
    );
    v___x_4453_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(
            v_msg_4428_,
            v___y_4430_,
            v___y_4431_,
            v___x_4452_,
            v___y_4433_,
        );
    leanh::lean_dec_ref_known(v___x_4452_, 14);
    return v___x_4453_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_ref_4454_: *mut leanh::LeanObject,
    mut v_msg_4455_: *mut leanh::LeanObject,
    mut v___y_4456_: *mut leanh::LeanObject,
    mut v___y_4457_: *mut leanh::LeanObject,
    mut v___y_4458_: *mut leanh::LeanObject,
    mut v___y_4459_: *mut leanh::LeanObject,
    mut v___y_4460_: *mut leanh::LeanObject,
    mut v___y_4461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4462_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_4454_, v_msg_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
    leanh::lean_dec(v___y_4460_);
    leanh::lean_dec_ref(v___y_4459_);
    leanh::lean_dec(v___y_4458_);
    leanh::lean_dec_ref(v___y_4457_);
    leanh::lean_dec_ref(v___y_4456_);
    leanh::lean_dec(v_ref_4454_);
    return v_res_4462_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = leanh::lean_box(1);
    v___x_4464_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__3,
    );
    v___x_4465_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__1);
    v___x_4466_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4466_, 0, v___x_4465_);
    leanh::lean_ctor_set(v___x_4466_, 1, v___x_4464_);
    leanh::lean_ctor_set(v___x_4466_, 2, v___x_4463_);
    return v___x_4466_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__1;
    v___x_4469_ = l_Lean_stringToMessageData(v___x_4468_);
    return v___x_4469_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4471_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__3;
    v___x_4472_ = l_Lean_stringToMessageData(v___x_4471_);
    return v___x_4472_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__5;
    v___x_4475_ = l_Lean_stringToMessageData(v___x_4474_);
    return v___x_4475_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__7;
    v___x_4478_ = l_Lean_stringToMessageData(v___x_4477_);
    return v___x_4478_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__9;
    v___x_4481_ = l_Lean_stringToMessageData(v___x_4480_);
    return v___x_4481_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__11;
    v___x_4484_ = l_Lean_stringToMessageData(v___x_4483_);
    return v___x_4484_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__13;
    v___x_4487_ = l_Lean_stringToMessageData(v___x_4486_);
    return v___x_4487_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(
    mut v_msg_4488_: *mut leanh::LeanObject,
    mut v_declHint_4489_: *mut leanh::LeanObject,
    mut v___y_4490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v_isExporting_4495_: u8 = 0;
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4549_: u8 = 0;
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4492_ = lean_st_ref_get(v___y_4490_);
                v_env_4493_ = leanh::lean_ctor_get(v___x_4492_, 0);
                leanh::lean_inc_ref(v_env_4493_);
                leanh::lean_dec(v___x_4492_);
                v___x_4494_ = l_Lean_Name_isAnonymous(v_declHint_4489_);
                if v___x_4494_ == 0 {
                    v_isExporting_4495_ = leanh::lean_ctor_get_uint8(
                        v_env_4493_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4495_ == 0 {
                        leanh::lean_dec_ref(v_env_4493_);
                        leanh::lean_dec(v_declHint_4489_);
                        v___x_4496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4496_, 0, v_msg_4488_);
                        return v___x_4496_;
                    } else {
                        leanh::lean_inc_ref(v_env_4493_);
                        v___x_4497_ = l_Lean_Environment_setExporting(v_env_4493_, v___x_4494_);
                        leanh::lean_inc(v_declHint_4489_);
                        leanh::lean_inc_ref(v___x_4497_);
                        v___x_4498_ = l_Lean_Environment_contains(
                            v___x_4497_,
                            v_declHint_4489_,
                            v_isExporting_4495_,
                        );
                        if v___x_4498_ == 0 {
                            leanh::lean_dec_ref(v___x_4497_);
                            leanh::lean_dec_ref(v_env_4493_);
                            leanh::lean_dec(v_declHint_4489_);
                            v___x_4499_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4499_, 0, v_msg_4488_);
                            return v___x_4499_;
                        } else {
                            v___x_4500_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
                            v___x_4501_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__0);
                            v___x_4502_ = l_Lean_Options_empty;
                            v___x_4503_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_4503_, 0, v___x_4497_);
                            leanh::lean_ctor_set(v___x_4503_, 1, v___x_4500_);
                            leanh::lean_ctor_set(v___x_4503_, 2, v___x_4501_);
                            leanh::lean_ctor_set(v___x_4503_, 3, v___x_4502_);
                            leanh::lean_inc(v_declHint_4489_);
                            v___x_4504_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4489_, v___x_4494_);
                            v_c_4505_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_4505_, 0, v___x_4503_);
                            leanh::lean_ctor_set(v_c_4505_, 1, v___x_4504_);
                            v___x_4506_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4493_,
                                v_declHint_4489_,
                            );
                            if leanh::lean_obj_tag(v___x_4506_) == 0 {
                                leanh::lean_dec_ref(v_env_4493_);
                                leanh::lean_dec(v_declHint_4489_);
                                v___x_4507_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
                                v___x_4508_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4508_, 0, v___x_4507_);
                                leanh::lean_ctor_set(v___x_4508_, 1, v_c_4505_);
                                v___x_4509_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__4);
                                v___x_4510_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4510_, 0, v___x_4508_);
                                leanh::lean_ctor_set(v___x_4510_, 1, v___x_4509_);
                                v___x_4511_ = l_Lean_MessageData_note(v___x_4510_);
                                v___x_4512_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4512_, 0, v_msg_4488_);
                                leanh::lean_ctor_set(v___x_4512_, 1, v___x_4511_);
                                v___x_4513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4513_, 0, v___x_4512_);
                                return v___x_4513_;
                            } else {
                                v_val_4514_ = leanh::lean_ctor_get(v___x_4506_, 0);
                                v_isSharedCheck_4549_ =
                                    (!leanh::lean_is_exclusive(v___x_4506_)) as u8;
                                if v_isSharedCheck_4549_ == 0 {
                                    v___x_4516_ = v___x_4506_;
                                    v_isShared_4517_ = v_isSharedCheck_4549_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4514_);
                                    leanh::lean_dec(v___x_4506_);
                                    v___x_4516_ = leanh::lean_box(0);
                                    v_isShared_4517_ = v_isSharedCheck_4549_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4493_);
                    leanh::lean_dec(v_declHint_4489_);
                    v___x_4550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4550_, 0, v_msg_4488_);
                    return v___x_4550_;
                }
            }
            1 => {
                v___x_4518_ = leanh::lean_box(0);
                v___x_4519_ = l_Lean_Environment_header(v_env_4493_);
                leanh::lean_dec_ref(v_env_4493_);
                v___x_4520_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4519_);
                v_mod_4521_ = lean_array_get(v___x_4518_, v___x_4520_, v_val_4514_);
                leanh::lean_dec(v_val_4514_);
                leanh::lean_dec_ref(v___x_4520_);
                v___x_4522_ = l_Lean_isPrivateName(v_declHint_4489_);
                leanh::lean_dec(v_declHint_4489_);
                if v___x_4522_ == 0 {
                    v___x_4523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__6);
                    v___x_4524_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4524_, 0, v___x_4523_);
                    leanh::lean_ctor_set(v___x_4524_, 1, v_c_4505_);
                    v___x_4525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__8);
                    v___x_4526_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4526_, 0, v___x_4524_);
                    leanh::lean_ctor_set(v___x_4526_, 1, v___x_4525_);
                    v___x_4527_ = l_Lean_MessageData_ofName(v_mod_4521_);
                    v___x_4528_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4528_, 0, v___x_4526_);
                    leanh::lean_ctor_set(v___x_4528_, 1, v___x_4527_);
                    v___x_4529_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__10);
                    v___x_4530_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4530_, 0, v___x_4528_);
                    leanh::lean_ctor_set(v___x_4530_, 1, v___x_4529_);
                    v___x_4531_ = l_Lean_MessageData_note(v___x_4530_);
                    v___x_4532_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4532_, 0, v_msg_4488_);
                    leanh::lean_ctor_set(v___x_4532_, 1, v___x_4531_);
                    if v_isShared_4517_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4516_, 0);
                        leanh::lean_ctor_set(v___x_4516_, 0, v___x_4532_);
                        v___x_4534_ = v___x_4516_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
                        v___x_4534_ = v_reuseFailAlloc_4535_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4536_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__2);
                    v___x_4537_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4537_, 0, v___x_4536_);
                    leanh::lean_ctor_set(v___x_4537_, 1, v_c_4505_);
                    v___x_4538_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__12);
                    v___x_4539_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4539_, 0, v___x_4537_);
                    leanh::lean_ctor_set(v___x_4539_, 1, v___x_4538_);
                    v___x_4540_ = l_Lean_MessageData_ofName(v_mod_4521_);
                    v___x_4541_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4541_, 0, v___x_4539_);
                    leanh::lean_ctor_set(v___x_4541_, 1, v___x_4540_);
                    v___x_4542_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___closed__14);
                    v___x_4543_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4543_, 0, v___x_4541_);
                    leanh::lean_ctor_set(v___x_4543_, 1, v___x_4542_);
                    v___x_4544_ = l_Lean_MessageData_note(v___x_4543_);
                    v___x_4545_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4545_, 0, v_msg_4488_);
                    leanh::lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                    if v_isShared_4517_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4516_, 0);
                        leanh::lean_ctor_set(v___x_4516_, 0, v___x_4545_);
                        v___x_4547_ = v___x_4516_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
                        v___x_4547_ = v_reuseFailAlloc_4548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4534_;
            }
            3 => {
                return v___x_4547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg___boxed(
    mut v_msg_4551_: *mut leanh::LeanObject,
    mut v_declHint_4552_: *mut leanh::LeanObject,
    mut v___y_4553_: *mut leanh::LeanObject,
    mut v___y_4554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4555_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_4551_, v_declHint_4552_, v___y_4553_);
    leanh::lean_dec(v___y_4553_);
    return v_res_4555_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(
    mut v_msg_4556_: *mut leanh::LeanObject,
    mut v_declHint_4557_: *mut leanh::LeanObject,
    mut v___y_4558_: *mut leanh::LeanObject,
    mut v___y_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_4556_, v_declHint_4557_, v___y_4562_);
                v_a_4565_ = leanh::lean_ctor_get(v___x_4564_, 0);
                v_isSharedCheck_4574_ = (!leanh::lean_is_exclusive(v___x_4564_)) as u8;
                if v_isSharedCheck_4574_ == 0 {
                    v___x_4567_ = v___x_4564_;
                    v_isShared_4568_ = v_isSharedCheck_4574_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4565_);
                    leanh::lean_dec(v___x_4564_);
                    v___x_4567_ = leanh::lean_box(0);
                    v_isShared_4568_ = v_isSharedCheck_4574_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4569_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4570_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4570_, 0, v___x_4569_);
                leanh::lean_ctor_set(v___x_4570_, 1, v_a_4565_);
                if v_isShared_4568_ == 0 {
                    leanh::lean_ctor_set(v___x_4567_, 0, v___x_4570_);
                    v___x_4572_ = v___x_4567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4573_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
                    v___x_4572_ = v_reuseFailAlloc_4573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_msg_4575_: *mut leanh::LeanObject,
    mut v_declHint_4576_: *mut leanh::LeanObject,
    mut v___y_4577_: *mut leanh::LeanObject,
    mut v___y_4578_: *mut leanh::LeanObject,
    mut v___y_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4583_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_4575_, v_declHint_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
    leanh::lean_dec(v___y_4581_);
    leanh::lean_dec_ref(v___y_4580_);
    leanh::lean_dec(v___y_4579_);
    leanh::lean_dec_ref(v___y_4578_);
    leanh::lean_dec_ref(v___y_4577_);
    return v_res_4583_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_ref_4584_: *mut leanh::LeanObject,
    mut v_msg_4585_: *mut leanh::LeanObject,
    mut v_declHint_4586_: *mut leanh::LeanObject,
    mut v___y_4587_: *mut leanh::LeanObject,
    mut v___y_4588_: *mut leanh::LeanObject,
    mut v___y_4589_: *mut leanh::LeanObject,
    mut v___y_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6(v_msg_4585_, v_declHint_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
    v_a_4594_ = leanh::lean_ctor_get(v___x_4593_, 0);
    leanh::lean_inc(v_a_4594_);
    leanh::lean_dec_ref(v___x_4593_);
    v___x_4595_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_4584_, v_a_4594_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
    return v___x_4595_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_4596_: *mut leanh::LeanObject,
    mut v_msg_4597_: *mut leanh::LeanObject,
    mut v_declHint_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
    mut v___y_4603_: *mut leanh::LeanObject,
    mut v___y_4604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4605_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4596_, v_msg_4597_, v_declHint_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
    leanh::lean_dec(v___y_4603_);
    leanh::lean_dec_ref(v___y_4602_);
    leanh::lean_dec(v___y_4601_);
    leanh::lean_dec_ref(v___y_4600_);
    leanh::lean_dec_ref(v___y_4599_);
    leanh::lean_dec(v_ref_4596_);
    return v_res_4605_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__0;
    v___x_4608_ = l_Lean_stringToMessageData(v___x_4607_);
    return v___x_4608_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4610_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__2;
    v___x_4611_ = l_Lean_stringToMessageData(v___x_4610_);
    return v___x_4611_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(
    mut v_ref_4612_: *mut leanh::LeanObject,
    mut v_constName_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___y_4617_: *mut leanh::LeanObject,
    mut v___y_4618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: u8 = 0;
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__1);
    v___x_4621_ = 0;
    leanh::lean_inc(v_constName_4613_);
    v___x_4622_ = l_Lean_MessageData_ofConstName(v_constName_4613_, v___x_4621_);
    v___x_4623_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4623_, 0, v___x_4620_);
    leanh::lean_ctor_set(v___x_4623_, 1, v___x_4622_);
    v___x_4624_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___closed__3);
    v___x_4625_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4625_, 0, v___x_4623_);
    leanh::lean_ctor_set(v___x_4625_, 1, v___x_4624_);
    v___x_4626_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4612_, v___x_4625_, v_constName_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
    return v___x_4626_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_ref_4627_: *mut leanh::LeanObject,
    mut v_constName_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
    mut v___y_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_4627_, v_constName_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
    leanh::lean_dec(v___y_4633_);
    leanh::lean_dec_ref(v___y_4632_);
    leanh::lean_dec(v___y_4631_);
    leanh::lean_dec_ref(v___y_4630_);
    leanh::lean_dec_ref(v___y_4629_);
    leanh::lean_dec(v_ref_4627_);
    return v_res_4635_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(
    mut v_constName_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: *mut leanh::LeanObject,
    mut v___y_4638_: *mut leanh::LeanObject,
    mut v___y_4639_: *mut leanh::LeanObject,
    mut v___y_4640_: *mut leanh::LeanObject,
    mut v___y_4641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4643_ = leanh::lean_ctor_get(v___y_4640_, 5);
    v___x_4644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_4643_, v_constName_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
    return v___x_4644_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg___boxed(
    mut v_constName_4645_: *mut leanh::LeanObject,
    mut v___y_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
    leanh::lean_dec(v___y_4650_);
    leanh::lean_dec_ref(v___y_4649_);
    leanh::lean_dec(v___y_4648_);
    leanh::lean_dec_ref(v___y_4647_);
    leanh::lean_dec_ref(v___y_4646_);
    return v_res_4652_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(
    mut v_constName_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: u8 = 0;
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4668_: u8 = 0;
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4660_ = lean_st_ref_get(v___y_4658_);
                v_env_4661_ = leanh::lean_ctor_get(v___x_4660_, 0);
                leanh::lean_inc_ref(v_env_4661_);
                leanh::lean_dec(v___x_4660_);
                v___x_4662_ = 0;
                leanh::lean_inc(v_constName_4653_);
                v___x_4663_ =
                    l_Lean_Environment_find_x3f(v_env_4661_, v_constName_4653_, v___x_4662_);
                if leanh::lean_obj_tag(v___x_4663_) == 0 {
                    v___x_4664_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
                    return v___x_4664_;
                } else {
                    leanh::lean_dec(v_constName_4653_);
                    v_val_4665_ = leanh::lean_ctor_get(v___x_4663_, 0);
                    v_isSharedCheck_4672_ = (!leanh::lean_is_exclusive(v___x_4663_)) as u8;
                    if v_isSharedCheck_4672_ == 0 {
                        v___x_4667_ = v___x_4663_;
                        v_isShared_4668_ = v_isSharedCheck_4672_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4665_);
                        leanh::lean_dec(v___x_4663_);
                        v___x_4667_ = leanh::lean_box(0);
                        v_isShared_4668_ = v_isSharedCheck_4672_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4668_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4667_, 0);
                    v___x_4670_ = v___x_4667_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_val_4665_);
                    v___x_4670_ = v_reuseFailAlloc_4671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1___boxed(
    mut v_constName_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
    mut v___y_4675_: *mut leanh::LeanObject,
    mut v___y_4676_: *mut leanh::LeanObject,
    mut v___y_4677_: *mut leanh::LeanObject,
    mut v___y_4678_: *mut leanh::LeanObject,
    mut v___y_4679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4680_ =
        l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(
            v_constName_4673_,
            v___y_4674_,
            v___y_4675_,
            v___y_4676_,
            v___y_4677_,
            v___y_4678_,
        );
    leanh::lean_dec(v___y_4678_);
    leanh::lean_dec_ref(v___y_4677_);
    leanh::lean_dec(v___y_4676_);
    leanh::lean_dec_ref(v___y_4675_);
    leanh::lean_dec_ref(v___y_4674_);
    return v_res_4680_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(
    mut v_structName_4681_: *mut leanh::LeanObject,
    mut v_idx_4682_: *mut leanh::LeanObject,
    mut v_s_4683_: *mut leanh::LeanObject,
    mut v_a_4684_: *mut leanh::LeanObject,
    mut v_a_4685_: *mut leanh::LeanObject,
    mut v_a_4686_: *mut leanh::LeanObject,
    mut v_a_4687_: *mut leanh::LeanObject,
    mut v_a_4688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut v___x_4709_: u8 = 0;
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: u8 = 0;
    let mut v_toConstantVal_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v_fst_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: u8 = 0;
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4770_: u8 = 0;
    let mut v_a_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4778_: u8 = 0;
    let mut v_reuseFailAlloc_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4783_: u8 = 0;
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut v_unused_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_s_4683_);
                v___x_4702_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(
                    v_s_4683_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_,
                );
                if leanh::lean_obj_tag(v___x_4702_) == 0 {
                    v_a_4703_ = leanh::lean_ctor_get(v___x_4702_, 0);
                    v_isSharedCheck_4798_ = (!leanh::lean_is_exclusive(v___x_4702_)) as u8;
                    if v_isSharedCheck_4798_ == 0 {
                        v___x_4705_ = v___x_4702_;
                        v_isShared_4706_ = v_isSharedCheck_4798_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4703_);
                        leanh::lean_dec(v___x_4702_);
                        v___x_4705_ = leanh::lean_box(0);
                        v_isShared_4706_ = v_isSharedCheck_4798_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_s_4683_);
                    leanh::lean_dec(v_idx_4682_);
                    leanh::lean_dec(v_structName_4681_);
                    return v___x_4702_;
                }
            }
            1 => {
                v___x_4696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg___closed__1);
                v___x_4697_ = l_Lean_mkFVar(v_s_4683_);
                v___x_4698_ = l_Lean_mkProj(v_structName_4681_, v_idx_4682_, v___x_4697_);
                v___x_4699_ = l_Lean_indentExpr(v___x_4698_);
                v___x_4700_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4700_, 0, v___x_4696_);
                leanh::lean_ctor_set(v___x_4700_, 1, v___x_4699_);
                v___x_4701_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg(v___x_4700_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
                return v___x_4701_;
            }
            2 => {
                v___x_4707_ = l_Lean_Expr_headBeta(v_a_4703_);
                v___x_4708_ = l_Lean_Expr_isErased(v___x_4707_);
                if v___x_4708_ == 0 {
                    v___x_4709_ = l_Lean_Expr_isAny(v___x_4707_);
                    if v___x_4709_ == 0 {
                        leanh::lean_del_object(v___x_4705_);
                        v___x_4710_ = l_Lean_Expr_getAppFn(v___x_4707_);
                        if leanh::lean_obj_tag(v___x_4710_) == 4 {
                            v_declName_4711_ = leanh::lean_ctor_get(v___x_4710_, 0);
                            leanh::lean_inc(v_declName_4711_);
                            v_us_4712_ = leanh::lean_ctor_get(v___x_4710_, 1);
                            leanh::lean_inc(v_us_4712_);
                            leanh::lean_dec_ref_known(v___x_4710_, 2);
                            v___x_4713_ = lean_st_ref_get(v_a_4688_);
                            v_env_4714_ = leanh::lean_ctor_get(v___x_4713_, 0);
                            leanh::lean_inc_ref(v_env_4714_);
                            leanh::lean_dec(v___x_4713_);
                            v___x_4715_ = l_Lean_Environment_find_x3f(
                                v_env_4714_,
                                v_declName_4711_,
                                v___x_4709_,
                            );
                            if leanh::lean_obj_tag(v___x_4715_) == 0 {
                                leanh::lean_dec(v_us_4712_);
                                leanh::lean_dec_ref(v___x_4707_);
                                v___y_4691_ = v_a_4684_;
                                v___y_4692_ = v_a_4685_;
                                v___y_4693_ = v_a_4686_;
                                v___y_4694_ = v_a_4687_;
                                v___y_4695_ = v_a_4688_;
                                state = 1;
                                continue;
                            } else {
                                v_val_4716_ = leanh::lean_ctor_get(v___x_4715_, 0);
                                leanh::lean_inc(v_val_4716_);
                                leanh::lean_dec_ref_known(v___x_4715_, 1);
                                if leanh::lean_obj_tag(v_val_4716_) == 5 {
                                    v_val_4717_ = leanh::lean_ctor_get(v_val_4716_, 0);
                                    leanh::lean_inc_ref(v_val_4717_);
                                    leanh::lean_dec_ref_known(v_val_4716_, 1);
                                    v_ctors_4718_ = leanh::lean_ctor_get(v_val_4717_, 4);
                                    leanh::lean_inc(v_ctors_4718_);
                                    if leanh::lean_obj_tag(v_ctors_4718_) == 1 {
                                        v_tail_4719_ =
                                            leanh::lean_ctor_get(v_ctors_4718_, 1);
                                        if leanh::lean_obj_tag(v_tail_4719_) == 0 {
                                            v_numParams_4720_ =
                                                leanh::lean_ctor_get(v_val_4717_, 1);
                                            leanh::lean_inc(v_numParams_4720_);
                                            v_numIndices_4721_ =
                                                leanh::lean_ctor_get(v_val_4717_, 2);
                                            leanh::lean_inc(v_numIndices_4721_);
                                            leanh::lean_dec_ref(v_val_4717_);
                                            v_head_4722_ =
                                                leanh::lean_ctor_get(v_ctors_4718_, 0);
                                            v_isSharedCheck_4788_ =
                                                (!leanh::lean_is_exclusive(v_ctors_4718_))
                                                    as u8;
                                            if v_isSharedCheck_4788_ == 0 {
                                                v_unused_4789_ =
                                                    leanh::lean_ctor_get(v_ctors_4718_, 1);
                                                leanh::lean_dec(v_unused_4789_);
                                                v___x_4724_ = v_ctors_4718_;
                                                v_isShared_4725_ = v_isSharedCheck_4788_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_head_4722_);
                                                leanh::lean_dec(v_ctors_4718_);
                                                v___x_4724_ = leanh::lean_box(0);
                                                v_isShared_4725_ = v_isSharedCheck_4788_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_ctors_4718_, 2);
                                            leanh::lean_dec_ref(v_val_4717_);
                                            leanh::lean_dec(v_us_4712_);
                                            leanh::lean_dec_ref(v___x_4707_);
                                            v___y_4691_ = v_a_4684_;
                                            v___y_4692_ = v_a_4685_;
                                            v___y_4693_ = v_a_4686_;
                                            v___y_4694_ = v_a_4687_;
                                            v___y_4695_ = v_a_4688_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_ctors_4718_);
                                        leanh::lean_dec_ref(v_val_4717_);
                                        leanh::lean_dec(v_us_4712_);
                                        leanh::lean_dec_ref(v___x_4707_);
                                        v___y_4691_ = v_a_4684_;
                                        v___y_4692_ = v_a_4685_;
                                        v___y_4693_ = v_a_4686_;
                                        v___y_4694_ = v_a_4687_;
                                        v___y_4695_ = v_a_4688_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_4716_);
                                    leanh::lean_dec(v_us_4712_);
                                    leanh::lean_dec_ref(v___x_4707_);
                                    v___y_4691_ = v_a_4684_;
                                    v___y_4692_ = v_a_4685_;
                                    v___y_4693_ = v_a_4686_;
                                    v___y_4694_ = v_a_4687_;
                                    v___y_4695_ = v_a_4688_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_4710_);
                            leanh::lean_dec_ref(v___x_4707_);
                            v___y_4691_ = v_a_4684_;
                            v___y_4692_ = v_a_4685_;
                            v___y_4693_ = v_a_4686_;
                            v___y_4694_ = v_a_4687_;
                            v___y_4695_ = v_a_4688_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_4707_);
                        leanh::lean_dec(v_s_4683_);
                        leanh::lean_dec(v_idx_4682_);
                        leanh::lean_dec(v_structName_4681_);
                        v___x_4790_ = l_Lean_Compiler_LCNF_anyExpr;
                        if v_isShared_4706_ == 0 {
                            leanh::lean_ctor_set(v___x_4705_, 0, v___x_4790_);
                            v___x_4792_ = v___x_4705_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_4793_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
                            v___x_4792_ = v_reuseFailAlloc_4793_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4707_);
                    leanh::lean_dec(v_s_4683_);
                    leanh::lean_dec(v_idx_4682_);
                    leanh::lean_dec(v_structName_4681_);
                    v___x_4794_ = l_Lean_Compiler_LCNF_erasedExpr;
                    if v_isShared_4706_ == 0 {
                        leanh::lean_ctor_set(v___x_4705_, 0, v___x_4794_);
                        v___x_4796_ = v___x_4705_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
                        v___x_4796_ = v_reuseFailAlloc_4797_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4726_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1(v_head_4722_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
                if leanh::lean_obj_tag(v___x_4726_) == 0 {
                    v_a_4727_ = leanh::lean_ctor_get(v___x_4726_, 0);
                    leanh::lean_inc(v_a_4727_);
                    leanh::lean_dec_ref_known(v___x_4726_, 1);
                    if leanh::lean_obj_tag(v_a_4727_) == 6 {
                        v_val_4728_ = leanh::lean_ctor_get(v_a_4727_, 0);
                        leanh::lean_inc_ref(v_val_4728_);
                        leanh::lean_dec_ref_known(v_a_4727_, 1);
                        v_dummy_4729_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0_once
                            ),
                            _init_l_Lean_Compiler_LCNF_InferType_Pure_inferAppType___closed__0,
                        );
                        v_nargs_4730_ = l_Lean_Expr_getAppNumArgs(v___x_4707_);
                        leanh::lean_inc(v_nargs_4730_);
                        v___x_4731_ = lean_mk_array(v_nargs_4730_, v_dummy_4729_);
                        v___x_4732_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4733_ = lean_nat_sub(v_nargs_4730_, v___x_4732_);
                        leanh::lean_dec(v_nargs_4730_);
                        v___x_4734_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v___x_4707_,
                            v___x_4731_,
                            v___x_4733_,
                        );
                        v___x_4735_ = lean_nat_add(v_numParams_4720_, v_numIndices_4721_);
                        leanh::lean_dec(v_numIndices_4721_);
                        v___x_4736_ = lean_array_get_size(v___x_4734_);
                        v___x_4737_ = lean_nat_dec_eq(v___x_4735_, v___x_4736_);
                        leanh::lean_dec(v___x_4735_);
                        if v___x_4737_ == 0 {
                            leanh::lean_dec_ref(v___x_4734_);
                            leanh::lean_dec_ref(v_val_4728_);
                            leanh::lean_del_object(v___x_4724_);
                            leanh::lean_dec(v_numParams_4720_);
                            leanh::lean_dec(v_us_4712_);
                            v___y_4691_ = v_a_4684_;
                            v___y_4692_ = v_a_4685_;
                            v___y_4693_ = v_a_4686_;
                            v___y_4694_ = v_a_4687_;
                            v___y_4695_ = v_a_4688_;
                            state = 1;
                            continue;
                        } else {
                            if v___x_4709_ == 0 {
                                v_toConstantVal_4738_ = leanh::lean_ctor_get(v_val_4728_, 0);
                                leanh::lean_inc_ref(v_toConstantVal_4738_);
                                leanh::lean_dec_ref(v_val_4728_);
                                v_name_4739_ =
                                    leanh::lean_ctor_get(v_toConstantVal_4738_, 0);
                                leanh::lean_inc(v_name_4739_);
                                leanh::lean_dec_ref(v_toConstantVal_4738_);
                                v___x_4740_ = l_Lean_mkConst(v_name_4739_, v_us_4712_);
                                v___x_4741_ = leanh::lean_unsigned_to_nat(0);
                                v___x_4742_ = l_Array_toSubarray___redArg(
                                    v___x_4734_,
                                    v___x_4741_,
                                    v_numParams_4720_,
                                );
                                v___x_4743_ = l_Subarray_copy___redArg(v___x_4742_);
                                v___x_4744_ = l_Lean_mkAppN(v___x_4740_, v___x_4743_);
                                leanh::lean_dec_ref(v___x_4743_);
                                v___x_4745_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppType(
                                    v___x_4744_,
                                    v_a_4684_,
                                    v_a_4685_,
                                    v_a_4686_,
                                    v_a_4687_,
                                    v_a_4688_,
                                );
                                if leanh::lean_obj_tag(v___x_4745_) == 0 {
                                    v_a_4746_ = leanh::lean_ctor_get(v___x_4745_, 0);
                                    leanh::lean_inc(v_a_4746_);
                                    leanh::lean_dec_ref_known(v___x_4745_, 1);
                                    v___x_4747_ = leanh::lean_box(0);
                                    if v_isShared_4725_ == 0 {
                                        leanh::lean_ctor_set_tag(v___x_4724_, 0);
                                        leanh::lean_ctor_set(v___x_4724_, 1, v_a_4746_);
                                        leanh::lean_ctor_set(v___x_4724_, 0, v___x_4747_);
                                        v___x_4749_ = v___x_4724_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4779_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4779_,
                                            0,
                                            v___x_4747_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4779_,
                                            1,
                                            v_a_4746_,
                                        );
                                        v___x_4749_ = v_reuseFailAlloc_4779_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_4724_);
                                    leanh::lean_dec(v_s_4683_);
                                    leanh::lean_dec(v_idx_4682_);
                                    leanh::lean_dec(v_structName_4681_);
                                    return v___x_4745_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4734_);
                                leanh::lean_dec_ref(v_val_4728_);
                                leanh::lean_del_object(v___x_4724_);
                                leanh::lean_dec(v_numParams_4720_);
                                leanh::lean_dec(v_us_4712_);
                                v___y_4691_ = v_a_4684_;
                                v___y_4692_ = v_a_4685_;
                                v___y_4693_ = v_a_4686_;
                                v___y_4694_ = v_a_4687_;
                                v___y_4695_ = v_a_4688_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4727_);
                        leanh::lean_del_object(v___x_4724_);
                        leanh::lean_dec(v_numIndices_4721_);
                        leanh::lean_dec(v_numParams_4720_);
                        leanh::lean_dec(v_us_4712_);
                        leanh::lean_dec_ref(v___x_4707_);
                        v___y_4691_ = v_a_4684_;
                        v___y_4692_ = v_a_4685_;
                        v___y_4693_ = v_a_4686_;
                        v___y_4694_ = v_a_4687_;
                        v___y_4695_ = v_a_4688_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4724_);
                    leanh::lean_dec(v_numIndices_4721_);
                    leanh::lean_dec(v_numParams_4720_);
                    leanh::lean_dec(v_us_4712_);
                    leanh::lean_dec_ref(v___x_4707_);
                    leanh::lean_dec(v_s_4683_);
                    leanh::lean_dec(v_idx_4682_);
                    leanh::lean_dec(v_structName_4681_);
                    v_a_4780_ = leanh::lean_ctor_get(v___x_4726_, 0);
                    v_isSharedCheck_4787_ = (!leanh::lean_is_exclusive(v___x_4726_)) as u8;
                    if v_isSharedCheck_4787_ == 0 {
                        v___x_4782_ = v___x_4726_;
                        v_isShared_4783_ = v_isSharedCheck_4787_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4780_);
                        leanh::lean_dec(v___x_4726_);
                        v___x_4782_ = leanh::lean_box(0);
                        v_isShared_4783_ = v_isSharedCheck_4787_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc(v_structName_4681_);
                leanh::lean_inc(v_s_4683_);
                leanh::lean_inc(v_idx_4682_);
                v___x_4750_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_idx_4682_, v_s_4683_, v_structName_4681_, v_idx_4682_, v___x_4741_, v___x_4749_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_);
                if leanh::lean_obj_tag(v___x_4750_) == 0 {
                    v_a_4751_ = leanh::lean_ctor_get(v___x_4750_, 0);
                    v_isSharedCheck_4770_ = (!leanh::lean_is_exclusive(v___x_4750_)) as u8;
                    if v_isSharedCheck_4770_ == 0 {
                        v___x_4753_ = v___x_4750_;
                        v_isShared_4754_ = v_isSharedCheck_4770_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4751_);
                        leanh::lean_dec(v___x_4750_);
                        v___x_4753_ = leanh::lean_box(0);
                        v_isShared_4754_ = v_isSharedCheck_4770_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_s_4683_);
                    leanh::lean_dec(v_idx_4682_);
                    leanh::lean_dec(v_structName_4681_);
                    v_a_4771_ = leanh::lean_ctor_get(v___x_4750_, 0);
                    v_isSharedCheck_4778_ = (!leanh::lean_is_exclusive(v___x_4750_)) as u8;
                    if v_isSharedCheck_4778_ == 0 {
                        v___x_4773_ = v___x_4750_;
                        v_isShared_4774_ = v_isSharedCheck_4778_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4771_);
                        leanh::lean_dec(v___x_4750_);
                        v___x_4773_ = leanh::lean_box(0);
                        v_isShared_4774_ = v_isSharedCheck_4778_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_fst_4755_ = leanh::lean_ctor_get(v_a_4751_, 0);
                if leanh::lean_obj_tag(v_fst_4755_) == 0 {
                    v_snd_4756_ = leanh::lean_ctor_get(v_a_4751_, 1);
                    leanh::lean_inc(v_snd_4756_);
                    leanh::lean_dec(v_a_4751_);
                    if leanh::lean_obj_tag(v_snd_4756_) == 7 {
                        leanh::lean_dec(v_s_4683_);
                        leanh::lean_dec(v_idx_4682_);
                        leanh::lean_dec(v_structName_4681_);
                        v_binderType_4757_ = leanh::lean_ctor_get(v_snd_4756_, 1);
                        leanh::lean_inc_ref(v_binderType_4757_);
                        leanh::lean_dec_ref_known(v_snd_4756_, 3);
                        if v_isShared_4754_ == 0 {
                            leanh::lean_ctor_set(v___x_4753_, 0, v_binderType_4757_);
                            v___x_4759_ = v___x_4753_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4760_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4760_,
                                0,
                                v_binderType_4757_,
                            );
                            v___x_4759_ = v_reuseFailAlloc_4760_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_4761_ = l_Lean_Expr_isErased(v_snd_4756_);
                        leanh::lean_dec(v_snd_4756_);
                        if v___x_4761_ == 0 {
                            leanh::lean_del_object(v___x_4753_);
                            v___y_4691_ = v_a_4684_;
                            v___y_4692_ = v_a_4685_;
                            v___y_4693_ = v_a_4686_;
                            v___y_4694_ = v_a_4687_;
                            v___y_4695_ = v_a_4688_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_s_4683_);
                            leanh::lean_dec(v_idx_4682_);
                            leanh::lean_dec(v_structName_4681_);
                            v___x_4762_ = l_Lean_Compiler_LCNF_erasedExpr;
                            if v_isShared_4754_ == 0 {
                                leanh::lean_ctor_set(v___x_4753_, 0, v___x_4762_);
                                v___x_4764_ = v___x_4753_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4765_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
                                v___x_4764_ = v_reuseFailAlloc_4765_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4755_);
                    leanh::lean_dec(v_a_4751_);
                    leanh::lean_dec(v_s_4683_);
                    leanh::lean_dec(v_idx_4682_);
                    leanh::lean_dec(v_structName_4681_);
                    v_val_4766_ = leanh::lean_ctor_get(v_fst_4755_, 0);
                    leanh::lean_inc(v_val_4766_);
                    leanh::lean_dec_ref_known(v_fst_4755_, 1);
                    if v_isShared_4754_ == 0 {
                        leanh::lean_ctor_set(v___x_4753_, 0, v_val_4766_);
                        v___x_4768_ = v___x_4753_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_val_4766_);
                        v___x_4768_ = v_reuseFailAlloc_4769_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4759_;
            }
            7 => {
                return v___x_4764_;
            }
            8 => {
                return v___x_4768_;
            }
            9 => {
                if v_isShared_4774_ == 0 {
                    v___x_4776_ = v___x_4773_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
                    v___x_4776_ = v_reuseFailAlloc_4777_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4776_;
            }
            11 => {
                if v_isShared_4783_ == 0 {
                    v___x_4785_ = v___x_4782_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4785_;
            }
            13 => {
                return v___x_4792_;
            }
            14 => {
                return v___x_4796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferProjType___boxed(
    mut v_structName_4799_: *mut leanh::LeanObject,
    mut v_idx_4800_: *mut leanh::LeanObject,
    mut v_s_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v_a_4805_: *mut leanh::LeanObject,
    mut v_a_4806_: *mut leanh::LeanObject,
    mut v_a_4807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4808_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(
        v_structName_4799_,
        v_idx_4800_,
        v_s_4801_,
        v_a_4802_,
        v_a_4803_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
    );
    leanh::lean_dec(v_a_4806_);
    leanh::lean_dec_ref(v_a_4805_);
    leanh::lean_dec(v_a_4804_);
    leanh::lean_dec_ref(v_a_4803_);
    leanh::lean_dec_ref(v_a_4802_);
    return v_res_4808_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(
    mut v_upperBound_4809_: *mut leanh::LeanObject,
    mut v_s_4810_: *mut leanh::LeanObject,
    mut v_structName_4811_: *mut leanh::LeanObject,
    mut v_idx_4812_: *mut leanh::LeanObject,
    mut v_inst_4813_: *mut leanh::LeanObject,
    mut v_R_4814_: *mut leanh::LeanObject,
    mut v_a_4815_: *mut leanh::LeanObject,
    mut v_b_4816_: *mut leanh::LeanObject,
    mut v_c_4817_: *mut leanh::LeanObject,
    mut v___y_4818_: *mut leanh::LeanObject,
    mut v___y_4819_: *mut leanh::LeanObject,
    mut v___y_4820_: *mut leanh::LeanObject,
    mut v___y_4821_: *mut leanh::LeanObject,
    mut v___y_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___redArg(v_upperBound_4809_, v_s_4810_, v_structName_4811_, v_idx_4812_, v_a_4815_, v_b_4816_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
    return v___x_4824_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2___boxed(
    mut v_upperBound_4825_: *mut leanh::LeanObject,
    mut v_s_4826_: *mut leanh::LeanObject,
    mut v_structName_4827_: *mut leanh::LeanObject,
    mut v_idx_4828_: *mut leanh::LeanObject,
    mut v_inst_4829_: *mut leanh::LeanObject,
    mut v_R_4830_: *mut leanh::LeanObject,
    mut v_a_4831_: *mut leanh::LeanObject,
    mut v_b_4832_: *mut leanh::LeanObject,
    mut v_c_4833_: *mut leanh::LeanObject,
    mut v___y_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
    mut v___y_4837_: *mut leanh::LeanObject,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2(v_upperBound_4825_, v_s_4826_, v_structName_4827_, v_idx_4828_, v_inst_4829_, v_R_4830_, v_a_4831_, v_b_4832_, v_c_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
    leanh::lean_dec(v___y_4838_);
    leanh::lean_dec_ref(v___y_4837_);
    leanh::lean_dec(v___y_4836_);
    leanh::lean_dec_ref(v___y_4835_);
    leanh::lean_dec_ref(v___y_4834_);
    leanh::lean_dec(v_a_4831_);
    leanh::lean_dec(v_upperBound_4825_);
    return v_res_4840_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(
    mut v_00_u03b1_4841_: *mut leanh::LeanObject,
    mut v_constName_4842_: *mut leanh::LeanObject,
    mut v___y_4843_: *mut leanh::LeanObject,
    mut v___y_4844_: *mut leanh::LeanObject,
    mut v___y_4845_: *mut leanh::LeanObject,
    mut v___y_4846_: *mut leanh::LeanObject,
    mut v___y_4847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4849_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___redArg(v_constName_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
    return v___x_4849_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1___boxed(
    mut v_00_u03b1_4850_: *mut leanh::LeanObject,
    mut v_constName_4851_: *mut leanh::LeanObject,
    mut v___y_4852_: *mut leanh::LeanObject,
    mut v___y_4853_: *mut leanh::LeanObject,
    mut v___y_4854_: *mut leanh::LeanObject,
    mut v___y_4855_: *mut leanh::LeanObject,
    mut v___y_4856_: *mut leanh::LeanObject,
    mut v___y_4857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1(v_00_u03b1_4850_, v_constName_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
    leanh::lean_dec(v___y_4856_);
    leanh::lean_dec_ref(v___y_4855_);
    leanh::lean_dec(v___y_4854_);
    leanh::lean_dec_ref(v___y_4853_);
    leanh::lean_dec_ref(v___y_4852_);
    return v_res_4858_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(
    mut v_upperBound_4859_: *mut leanh::LeanObject,
    mut v_s_4860_: *mut leanh::LeanObject,
    mut v_structName_4861_: *mut leanh::LeanObject,
    mut v_idx_4862_: *mut leanh::LeanObject,
    mut v_inst_4863_: *mut leanh::LeanObject,
    mut v_R_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_b_4866_: *mut leanh::LeanObject,
    mut v_c_4867_: *mut leanh::LeanObject,
    mut v___y_4868_: *mut leanh::LeanObject,
    mut v___y_4869_: *mut leanh::LeanObject,
    mut v___y_4870_: *mut leanh::LeanObject,
    mut v___y_4871_: *mut leanh::LeanObject,
    mut v___y_4872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4874_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___redArg(v_upperBound_4859_, v_s_4860_, v_structName_4861_, v_idx_4862_, v_a_4865_, v_b_4866_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
    return v___x_4874_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3___boxed(
    mut v_upperBound_4875_: *mut leanh::LeanObject,
    mut v_s_4876_: *mut leanh::LeanObject,
    mut v_structName_4877_: *mut leanh::LeanObject,
    mut v_idx_4878_: *mut leanh::LeanObject,
    mut v_inst_4879_: *mut leanh::LeanObject,
    mut v_R_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
    mut v_b_4882_: *mut leanh::LeanObject,
    mut v_c_4883_: *mut leanh::LeanObject,
    mut v___y_4884_: *mut leanh::LeanObject,
    mut v___y_4885_: *mut leanh::LeanObject,
    mut v___y_4886_: *mut leanh::LeanObject,
    mut v___y_4887_: *mut leanh::LeanObject,
    mut v___y_4888_: *mut leanh::LeanObject,
    mut v___y_4889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4890_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__2_spec__3(v_upperBound_4875_, v_s_4876_, v_structName_4877_, v_idx_4878_, v_inst_4879_, v_R_4880_, v_a_4881_, v_b_4882_, v_c_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
    leanh::lean_dec(v___y_4888_);
    leanh::lean_dec_ref(v___y_4887_);
    leanh::lean_dec(v___y_4886_);
    leanh::lean_dec_ref(v___y_4885_);
    leanh::lean_dec_ref(v___y_4884_);
    leanh::lean_dec(v_upperBound_4875_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(
    mut v_00_u03b1_4891_: *mut leanh::LeanObject,
    mut v_ref_4892_: *mut leanh::LeanObject,
    mut v_constName_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
    mut v___y_4895_: *mut leanh::LeanObject,
    mut v___y_4896_: *mut leanh::LeanObject,
    mut v___y_4897_: *mut leanh::LeanObject,
    mut v___y_4898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4900_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___redArg(v_ref_4892_, v_constName_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
    return v___x_4900_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b1_4901_: *mut leanh::LeanObject,
    mut v_ref_4902_: *mut leanh::LeanObject,
    mut v_constName_4903_: *mut leanh::LeanObject,
    mut v___y_4904_: *mut leanh::LeanObject,
    mut v___y_4905_: *mut leanh::LeanObject,
    mut v___y_4906_: *mut leanh::LeanObject,
    mut v___y_4907_: *mut leanh::LeanObject,
    mut v___y_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4910_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2(v_00_u03b1_4901_, v_ref_4902_, v_constName_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
    leanh::lean_dec(v___y_4908_);
    leanh::lean_dec_ref(v___y_4907_);
    leanh::lean_dec(v___y_4906_);
    leanh::lean_dec_ref(v___y_4905_);
    leanh::lean_dec_ref(v___y_4904_);
    leanh::lean_dec(v_ref_4902_);
    return v_res_4910_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b1_4911_: *mut leanh::LeanObject,
    mut v_ref_4912_: *mut leanh::LeanObject,
    mut v_msg_4913_: *mut leanh::LeanObject,
    mut v_declHint_4914_: *mut leanh::LeanObject,
    mut v___y_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___y_4918_: *mut leanh::LeanObject,
    mut v___y_4919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4921_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___redArg(v_ref_4912_, v_msg_4913_, v_declHint_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_);
    return v___x_4921_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_4922_: *mut leanh::LeanObject,
    mut v_ref_4923_: *mut leanh::LeanObject,
    mut v_msg_4924_: *mut leanh::LeanObject,
    mut v_declHint_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4932_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4(v_00_u03b1_4922_, v_ref_4923_, v_msg_4924_, v_declHint_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
    leanh::lean_dec(v___y_4930_);
    leanh::lean_dec_ref(v___y_4929_);
    leanh::lean_dec(v___y_4928_);
    leanh::lean_dec_ref(v___y_4927_);
    leanh::lean_dec_ref(v___y_4926_);
    leanh::lean_dec(v_ref_4923_);
    return v_res_4932_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msg_4933_: *mut leanh::LeanObject,
    mut v_declHint_4934_: *mut leanh::LeanObject,
    mut v___y_4935_: *mut leanh::LeanObject,
    mut v___y_4936_: *mut leanh::LeanObject,
    mut v___y_4937_: *mut leanh::LeanObject,
    mut v___y_4938_: *mut leanh::LeanObject,
    mut v___y_4939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4941_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___redArg(v_msg_4933_, v_declHint_4934_, v___y_4939_);
    return v___x_4941_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msg_4942_: *mut leanh::LeanObject,
    mut v_declHint_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
    mut v___y_4947_: *mut leanh::LeanObject,
    mut v___y_4948_: *mut leanh::LeanObject,
    mut v___y_4949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4950_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4942_, v_declHint_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
    leanh::lean_dec(v___y_4948_);
    leanh::lean_dec_ref(v___y_4947_);
    leanh::lean_dec(v___y_4946_);
    leanh::lean_dec_ref(v___y_4945_);
    leanh::lean_dec_ref(v___y_4944_);
    return v_res_4950_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b1_4951_: *mut leanh::LeanObject,
    mut v_ref_4952_: *mut leanh::LeanObject,
    mut v_msg_4953_: *mut leanh::LeanObject,
    mut v___y_4954_: *mut leanh::LeanObject,
    mut v___y_4955_: *mut leanh::LeanObject,
    mut v___y_4956_: *mut leanh::LeanObject,
    mut v___y_4957_: *mut leanh::LeanObject,
    mut v___y_4958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4960_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ref_4952_, v_msg_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
    return v___x_4960_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b1_4961_: *mut leanh::LeanObject,
    mut v_ref_4962_: *mut leanh::LeanObject,
    mut v_msg_4963_: *mut leanh::LeanObject,
    mut v___y_4964_: *mut leanh::LeanObject,
    mut v___y_4965_: *mut leanh::LeanObject,
    mut v___y_4966_: *mut leanh::LeanObject,
    mut v___y_4967_: *mut leanh::LeanObject,
    mut v___y_4968_: *mut leanh::LeanObject,
    mut v___y_4969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4970_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b1_4961_, v_ref_4962_, v_msg_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
    leanh::lean_dec(v___y_4968_);
    leanh::lean_dec_ref(v___y_4967_);
    leanh::lean_dec(v___y_4966_);
    leanh::lean_dec_ref(v___y_4965_);
    leanh::lean_dec_ref(v___y_4964_);
    leanh::lean_dec(v_ref_4962_);
    return v_res_4970_;
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(
    mut v_e_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
    mut v_a_4973_: *mut leanh::LeanObject,
    mut v_a_4974_: *mut leanh::LeanObject,
    mut v_a_4975_: *mut leanh::LeanObject,
    mut v_a_4976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4981_: u8 = 0;
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4986_: u8 = 0;
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_4971_) {
                0 => {
                    v_value_4978_ = leanh::lean_ctor_get(v_e_4971_, 0);
                    v_isSharedCheck_4986_ = (!leanh::lean_is_exclusive(v_e_4971_)) as u8;
                    if v_isSharedCheck_4986_ == 0 {
                        v___x_4980_ = v_e_4971_;
                        v_isShared_4981_ = v_isSharedCheck_4986_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4978_);
                        leanh::lean_dec(v_e_4971_);
                        v___x_4980_ = leanh::lean_box(0);
                        v_isShared_4981_ = v_isSharedCheck_4986_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4987_ = l_Lean_Compiler_LCNF_erasedExpr;
                    v___x_4988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4988_, 0, v___x_4987_);
                    return v___x_4988_;
                }
                2 => {
                    v_typeName_4989_ = leanh::lean_ctor_get(v_e_4971_, 0);
                    leanh::lean_inc(v_typeName_4989_);
                    v_idx_4990_ = leanh::lean_ctor_get(v_e_4971_, 1);
                    leanh::lean_inc(v_idx_4990_);
                    v_struct_4991_ = leanh::lean_ctor_get(v_e_4971_, 2);
                    leanh::lean_inc(v_struct_4991_);
                    leanh::lean_dec_ref_known(v_e_4971_, 3);
                    v___x_4992_ = l_Lean_Compiler_LCNF_InferType_Pure_inferProjType(
                        v_typeName_4989_,
                        v_idx_4990_,
                        v_struct_4991_,
                        v_a_4972_,
                        v_a_4973_,
                        v_a_4974_,
                        v_a_4975_,
                        v_a_4976_,
                    );
                    return v___x_4992_;
                }
                3 => {
                    v_declName_4993_ = leanh::lean_ctor_get(v_e_4971_, 0);
                    leanh::lean_inc(v_declName_4993_);
                    v_us_4994_ = leanh::lean_ctor_get(v_e_4971_, 1);
                    leanh::lean_inc(v_us_4994_);
                    v_args_4995_ = leanh::lean_ctor_get(v_e_4971_, 2);
                    leanh::lean_inc_ref(v_args_4995_);
                    leanh::lean_dec_ref_known(v_e_4971_, 3);
                    v___x_4996_ = l_Lean_Compiler_LCNF_InferType_Pure_inferConstType(
                        v_declName_4993_,
                        v_us_4994_,
                        v_a_4973_,
                        v_a_4974_,
                        v_a_4975_,
                        v_a_4976_,
                    );
                    if leanh::lean_obj_tag(v___x_4996_) == 0 {
                        v_a_4997_ = leanh::lean_ctor_get(v___x_4996_, 0);
                        leanh::lean_inc(v_a_4997_);
                        leanh::lean_dec_ref_known(v___x_4996_, 1);
                        v___x_4998_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(
                            v_a_4997_,
                            v_args_4995_,
                            v_a_4972_,
                            v_a_4973_,
                            v_a_4974_,
                            v_a_4975_,
                            v_a_4976_,
                        );
                        return v___x_4998_;
                    } else {
                        leanh::lean_dec_ref(v_args_4995_);
                        return v___x_4996_;
                    }
                }
                _ => {
                    v_fvarId_4999_ = leanh::lean_ctor_get(v_e_4971_, 0);
                    leanh::lean_inc(v_fvarId_4999_);
                    v_args_5000_ = leanh::lean_ctor_get(v_e_4971_, 1);
                    leanh::lean_inc_ref(v_args_5000_);
                    leanh::lean_dec_ref_known(v_e_4971_, 2);
                    v___x_5001_ = l_Lean_Compiler_LCNF_InferType_Pure_getType(
                        v_fvarId_4999_,
                        v_a_4972_,
                        v_a_4973_,
                        v_a_4974_,
                        v_a_4975_,
                        v_a_4976_,
                    );
                    if leanh::lean_obj_tag(v___x_5001_) == 0 {
                        v_a_5002_ = leanh::lean_ctor_get(v___x_5001_, 0);
                        leanh::lean_inc(v_a_5002_);
                        leanh::lean_dec_ref_known(v___x_5001_, 1);
                        v___x_5003_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(
                            v_a_5002_,
                            v_args_5000_,
                            v_a_4972_,
                            v_a_4973_,
                            v_a_4974_,
                            v_a_4975_,
                            v_a_4976_,
                        );
                        return v___x_5003_;
                    } else {
                        leanh::lean_dec_ref(v_args_5000_);
                        return v___x_5001_;
                    }
                }
            },
            1 => {
                v___x_4982_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLitValueType(v_value_4978_);
                leanh::lean_dec_ref(v_value_4978_);
                if v_isShared_4981_ == 0 {
                    leanh::lean_ctor_set(v___x_4980_, 0, v___x_4982_);
                    v___x_4984_ = v___x_4980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4985_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4985_, 0, v___x_4982_);
                    v___x_4984_ = v_reuseFailAlloc_4985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType___boxed(
    mut v_e_5004_: *mut leanh::LeanObject,
    mut v_a_5005_: *mut leanh::LeanObject,
    mut v_a_5006_: *mut leanh::LeanObject,
    mut v_a_5007_: *mut leanh::LeanObject,
    mut v_a_5008_: *mut leanh::LeanObject,
    mut v_a_5009_: *mut leanh::LeanObject,
    mut v_a_5010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5011_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(
        v_e_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_,
    );
    leanh::lean_dec(v_a_5009_);
    leanh::lean_dec_ref(v_a_5008_);
    leanh::lean_dec(v_a_5007_);
    leanh::lean_dec_ref(v_a_5006_);
    leanh::lean_dec_ref(v_a_5005_);
    return v_res_5011_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferType(
    mut v_e_5012_: *mut leanh::LeanObject,
    mut v_a_5013_: *mut leanh::LeanObject,
    mut v_a_5014_: *mut leanh::LeanObject,
    mut v_a_5015_: *mut leanh::LeanObject,
    mut v_a_5016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5018_ = leanh::lean_unsigned_to_nat(32);
    v___x_5019_ = lean_mk_empty_array_with_capacity(v___x_5018_);
    leanh::lean_dec_ref(v___x_5019_);
    v___x_5020_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4,
    );
    v___x_5021_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType(
        v_e_5012_,
        v___x_5020_,
        v_a_5013_,
        v_a_5014_,
        v_a_5015_,
        v_a_5016_,
    );
    return v___x_5021_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferType___boxed(
    mut v_e_5022_: *mut leanh::LeanObject,
    mut v_a_5023_: *mut leanh::LeanObject,
    mut v_a_5024_: *mut leanh::LeanObject,
    mut v_a_5025_: *mut leanh::LeanObject,
    mut v_a_5026_: *mut leanh::LeanObject,
    mut v_a_5027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5028_ =
        l_Lean_Compiler_LCNF_inferType(v_e_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
    leanh::lean_dec(v_a_5026_);
    leanh::lean_dec_ref(v_a_5025_);
    leanh::lean_dec(v_a_5024_);
    leanh::lean_dec_ref(v_a_5023_);
    return v_res_5028_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
    mut v_msg_5029_: *mut leanh::LeanObject,
    mut v___y_5030_: *mut leanh::LeanObject,
    mut v___y_5031_: *mut leanh::LeanObject,
    mut v___y_5032_: *mut leanh::LeanObject,
    mut v___y_5033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208__overap_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5035_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1,
    );
    v_toApplicative_5036_ = leanh::lean_ctor_get(v___x_5035_, 0);
    v_toFunctor_5037_ = leanh::lean_ctor_get(v_toApplicative_5036_, 0);
    v_toSeq_5038_ = leanh::lean_ctor_get(v_toApplicative_5036_, 2);
    v_toSeqLeft_5039_ = leanh::lean_ctor_get(v_toApplicative_5036_, 3);
    v_toSeqRight_5040_ = leanh::lean_ctor_get(v_toApplicative_5036_, 4);
    v___f_5041_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2;
    v___f_5042_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3;
    leanh::lean_inc_ref_n(v_toFunctor_5037_, 2);
    v___f_5043_ = leanh::lean_alloc_closure(
        l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5043_, 0, v_toFunctor_5037_);
    v___f_5044_ = leanh::lean_alloc_closure(
        l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5044_, 0, v_toFunctor_5037_);
    v___x_5045_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5045_, 0, v___f_5043_);
    leanh::lean_ctor_set(v___x_5045_, 1, v___f_5044_);
    leanh::lean_inc(v_toSeqRight_5040_);
    v___f_5046_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5046_, 0, v_toSeqRight_5040_);
    leanh::lean_inc(v_toSeqLeft_5039_);
    v___f_5047_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5047_, 0, v_toSeqLeft_5039_);
    leanh::lean_inc(v_toSeq_5038_);
    v___f_5048_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5048_, 0, v_toSeq_5038_);
    v___x_5049_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_5049_, 0, v___x_5045_);
    leanh::lean_ctor_set(v___x_5049_, 1, v___f_5041_);
    leanh::lean_ctor_set(v___x_5049_, 2, v___f_5048_);
    leanh::lean_ctor_set(v___x_5049_, 3, v___f_5047_);
    leanh::lean_ctor_set(v___x_5049_, 4, v___f_5046_);
    v___x_5050_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5050_, 0, v___x_5049_);
    leanh::lean_ctor_set(v___x_5050_, 1, v___f_5042_);
    v___x_5051_ = l_StateRefT_x27_instMonad___redArg(v___x_5050_);
    v___x_5052_ = l_Lean_instInhabitedExpr;
    v___x_5053_ = l_instInhabitedOfMonad___redArg(v___x_5051_, v___x_5052_);
    v___f_5054_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5054_, 0, v___x_5053_);
    v___x_208__overap_5055_ = lean_panic_fn_borrowed(v___f_5054_, v_msg_5029_);
    leanh::lean_dec_ref(v___f_5054_);
    leanh::lean_inc(v___y_5033_);
    leanh::lean_inc_ref(v___y_5032_);
    leanh::lean_inc(v___y_5031_);
    leanh::lean_inc_ref(v___y_5030_);
    v___x_5056_ = leanh::lean_apply_5(
        v___x_208__overap_5055_,
        v___y_5030_,
        v___y_5031_,
        v___y_5032_,
        v___y_5033_,
        leanh::lean_box(0),
    );
    return v___x_5056_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0___boxed(
    mut v_msg_5057_: *mut leanh::LeanObject,
    mut v___y_5058_: *mut leanh::LeanObject,
    mut v___y_5059_: *mut leanh::LeanObject,
    mut v___y_5060_: *mut leanh::LeanObject,
    mut v___y_5061_: *mut leanh::LeanObject,
    mut v___y_5062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
        v_msg_5057_,
        v___y_5058_,
        v___y_5059_,
        v___y_5060_,
        v___y_5061_,
    );
    leanh::lean_dec(v___y_5061_);
    leanh::lean_dec_ref(v___y_5060_);
    leanh::lean_dec(v___y_5059_);
    leanh::lean_dec_ref(v___y_5058_);
    return v_res_5063_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_inferAppType___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5066_ = l_Lean_Compiler_LCNF_inferAppType___closed__1;
    v___x_5067_ = leanh::lean_unsigned_to_nat(15);
    v___x_5068_ = leanh::lean_unsigned_to_nat(258);
    v___x_5069_ = l_Lean_Compiler_LCNF_inferAppType___closed__0;
    v___x_5070_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_5071_ = l_mkPanicMessageWithDecl(
        v___x_5070_,
        v___x_5069_,
        v___x_5068_,
        v___x_5067_,
        v___x_5066_,
    );
    return v___x_5071_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inferAppType(
    mut v_pu_5072_: u8,
    mut v_fnType_5073_: *mut leanh::LeanObject,
    mut v_args_5074_: *mut leanh::LeanObject,
    mut v_a_5075_: *mut leanh::LeanObject,
    mut v_a_5076_: *mut leanh::LeanObject,
    mut v_a_5077_: *mut leanh::LeanObject,
    mut v_a_5078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_5072_ == 0 {
        let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5080_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once
            ),
            _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4,
        );
        v___x_5081_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(
            v_fnType_5073_,
            v_args_5074_,
            v___x_5080_,
            v_a_5075_,
            v_a_5076_,
            v_a_5077_,
            v_a_5078_,
        );
        return v___x_5081_;
    } else {
        let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_args_5074_);
        leanh::lean_dec_ref(v_fnType_5073_);
        v___x_5082_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inferAppType___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_inferAppType___closed__2_once),
            _init_l_Lean_Compiler_LCNF_inferAppType___closed__2,
        );
        v___x_5083_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
            v___x_5082_,
            v_a_5075_,
            v_a_5076_,
            v_a_5077_,
            v_a_5078_,
        );
        return v___x_5083_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_inferAppType___boxed(
    mut v_pu_5084_: *mut leanh::LeanObject,
    mut v_fnType_5085_: *mut leanh::LeanObject,
    mut v_args_5086_: *mut leanh::LeanObject,
    mut v_a_5087_: *mut leanh::LeanObject,
    mut v_a_5088_: *mut leanh::LeanObject,
    mut v_a_5089_: *mut leanh::LeanObject,
    mut v_a_5090_: *mut leanh::LeanObject,
    mut v_a_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5092_: u8 = 0;
    let mut v_res_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5092_ = (leanh::lean_unbox(v_pu_5084_) as u8);
    v_res_5093_ = l_Lean_Compiler_LCNF_inferAppType(
        v_pu_boxed_5092_,
        v_fnType_5085_,
        v_args_5086_,
        v_a_5087_,
        v_a_5088_,
        v_a_5089_,
        v_a_5090_,
    );
    leanh::lean_dec(v_a_5090_);
    leanh::lean_dec_ref(v_a_5089_);
    leanh::lean_dec(v_a_5088_);
    leanh::lean_dec_ref(v_a_5087_);
    return v_res_5093_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5095_ = l_Lean_Compiler_LCNF_inferAppType___closed__1;
    v___x_5096_ = leanh::lean_unsigned_to_nat(15);
    v___x_5097_ = leanh::lean_unsigned_to_nat(263);
    v___x_5098_ = l_Lean_Compiler_LCNF_Arg_inferType___closed__0;
    v___x_5099_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_5100_ = l_mkPanicMessageWithDecl(
        v___x_5099_,
        v___x_5098_,
        v___x_5097_,
        v___x_5096_,
        v___x_5095_,
    );
    return v___x_5100_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_inferType(
    mut v_pu_5101_: u8,
    mut v_arg_5102_: *mut leanh::LeanObject,
    mut v_a_5103_: *mut leanh::LeanObject,
    mut v_a_5104_: *mut leanh::LeanObject,
    mut v_a_5105_: *mut leanh::LeanObject,
    mut v_a_5106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_5101_ == 0 {
        let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5108_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once
            ),
            _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4,
        );
        v___x_5109_ = l_Lean_Compiler_LCNF_InferType_Pure_inferArgType(
            v_arg_5102_,
            v___x_5108_,
            v_a_5103_,
            v_a_5104_,
            v_a_5105_,
            v_a_5106_,
        );
        return v___x_5109_;
    } else {
        let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_arg_5102_);
        v___x_5110_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Arg_inferType___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Arg_inferType___closed__1_once),
            _init_l_Lean_Compiler_LCNF_Arg_inferType___closed__1,
        );
        v___x_5111_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
            v___x_5110_,
            v_a_5103_,
            v_a_5104_,
            v_a_5105_,
            v_a_5106_,
        );
        return v___x_5111_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_inferType___boxed(
    mut v_pu_5112_: *mut leanh::LeanObject,
    mut v_arg_5113_: *mut leanh::LeanObject,
    mut v_a_5114_: *mut leanh::LeanObject,
    mut v_a_5115_: *mut leanh::LeanObject,
    mut v_a_5116_: *mut leanh::LeanObject,
    mut v_a_5117_: *mut leanh::LeanObject,
    mut v_a_5118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5119_: u8 = 0;
    let mut v_res_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5119_ = (leanh::lean_unbox(v_pu_5112_) as u8);
    v_res_5120_ = l_Lean_Compiler_LCNF_Arg_inferType(
        v_pu_boxed_5119_,
        v_arg_5113_,
        v_a_5114_,
        v_a_5115_,
        v_a_5116_,
        v_a_5117_,
    );
    leanh::lean_dec(v_a_5117_);
    leanh::lean_dec_ref(v_a_5116_);
    leanh::lean_dec(v_a_5115_);
    leanh::lean_dec_ref(v_a_5114_);
    return v_res_5120_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5122_ = l_Lean_Compiler_LCNF_inferAppType___closed__1;
    v___x_5123_ = leanh::lean_unsigned_to_nat(15);
    v___x_5124_ = leanh::lean_unsigned_to_nat(268);
    v___x_5125_ = l_Lean_Compiler_LCNF_LetValue_inferType___closed__0;
    v___x_5126_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_5127_ = l_mkPanicMessageWithDecl(
        v___x_5126_,
        v___x_5125_,
        v___x_5124_,
        v___x_5123_,
        v___x_5122_,
    );
    return v___x_5127_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_inferType(
    mut v_pu_5128_: u8,
    mut v_e_5129_: *mut leanh::LeanObject,
    mut v_a_5130_: *mut leanh::LeanObject,
    mut v_a_5131_: *mut leanh::LeanObject,
    mut v_a_5132_: *mut leanh::LeanObject,
    mut v_a_5133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_5128_ == 0 {
        let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5135_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once
            ),
            _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4,
        );
        v___x_5136_ = l_Lean_Compiler_LCNF_InferType_Pure_inferLetValueType(
            v_e_5129_,
            v___x_5135_,
            v_a_5130_,
            v_a_5131_,
            v_a_5132_,
            v_a_5133_,
        );
        return v___x_5136_;
    } else {
        let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_e_5129_);
        v___x_5137_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LetValue_inferType___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_LetValue_inferType___closed__1_once),
            _init_l_Lean_Compiler_LCNF_LetValue_inferType___closed__1,
        );
        v___x_5138_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
            v___x_5137_,
            v_a_5130_,
            v_a_5131_,
            v_a_5132_,
            v_a_5133_,
        );
        return v___x_5138_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_inferType___boxed(
    mut v_pu_5139_: *mut leanh::LeanObject,
    mut v_e_5140_: *mut leanh::LeanObject,
    mut v_a_5141_: *mut leanh::LeanObject,
    mut v_a_5142_: *mut leanh::LeanObject,
    mut v_a_5143_: *mut leanh::LeanObject,
    mut v_a_5144_: *mut leanh::LeanObject,
    mut v_a_5145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5146_: u8 = 0;
    let mut v_res_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5146_ = (leanh::lean_unbox(v_pu_5139_) as u8);
    v_res_5147_ = l_Lean_Compiler_LCNF_LetValue_inferType(
        v_pu_boxed_5146_,
        v_e_5140_,
        v_a_5141_,
        v_a_5142_,
        v_a_5143_,
        v_a_5144_,
    );
    leanh::lean_dec(v_a_5144_);
    leanh::lean_dec_ref(v_a_5143_);
    leanh::lean_dec(v_a_5142_);
    leanh::lean_dec_ref(v_a_5141_);
    return v_res_5147_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5149_ = l_Lean_Compiler_LCNF_inferAppType___closed__1;
    v___x_5150_ = leanh::lean_unsigned_to_nat(15);
    v___x_5151_ = leanh::lean_unsigned_to_nat(279);
    v___x_5152_ = l_Lean_Compiler_LCNF_Code_inferType___closed__0;
    v___x_5153_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_5154_ = l_mkPanicMessageWithDecl(
        v___x_5153_,
        v___x_5152_,
        v___x_5151_,
        v___x_5150_,
        v___x_5149_,
    );
    return v___x_5154_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_inferType(
    mut v_pu_5155_: u8,
    mut v_code_5156_: *mut leanh::LeanObject,
    mut v_a_5157_: *mut leanh::LeanObject,
    mut v_a_5158_: *mut leanh::LeanObject,
    mut v_a_5159_: *mut leanh::LeanObject,
    mut v_a_5160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5171_: u8 = 0;
    let mut v_resultType_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_fvarId_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5182_: u8 = 0;
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v_k_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_pu_5155_ == 0 {
                    match leanh::lean_obj_tag(v_code_5156_) {
                        3 => {
                            v_fvarId_5162_ = leanh::lean_ctor_get(v_code_5156_, 0);
                            leanh::lean_inc(v_fvarId_5162_);
                            v_args_5163_ = leanh::lean_ctor_get(v_code_5156_, 1);
                            leanh::lean_inc_ref(v_args_5163_);
                            leanh::lean_dec_ref_known(v_code_5156_, 2);
                            v___x_5164_ = l_Lean_Compiler_LCNF_getType(
                                v_fvarId_5162_,
                                v_a_5157_,
                                v_a_5158_,
                                v_a_5159_,
                                v_a_5160_,
                            );
                            if leanh::lean_obj_tag(v___x_5164_) == 0 {
                                v_a_5165_ = leanh::lean_ctor_get(v___x_5164_, 0);
                                leanh::lean_inc(v_a_5165_);
                                leanh::lean_dec_ref_known(v___x_5164_, 1);
                                v___x_5166_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once), _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4);
                                v___x_5167_ = l_Lean_Compiler_LCNF_InferType_Pure_inferAppTypeCore(
                                    v_a_5165_,
                                    v_args_5163_,
                                    v___x_5166_,
                                    v_a_5157_,
                                    v_a_5158_,
                                    v_a_5159_,
                                    v_a_5160_,
                                );
                                return v___x_5167_;
                            } else {
                                leanh::lean_dec_ref(v_args_5163_);
                                return v___x_5164_;
                            }
                        }
                        4 => {
                            v_cases_5168_ = leanh::lean_ctor_get(v_code_5156_, 0);
                            v_isSharedCheck_5176_ =
                                (!leanh::lean_is_exclusive(v_code_5156_)) as u8;
                            if v_isSharedCheck_5176_ == 0 {
                                v___x_5170_ = v_code_5156_;
                                v_isShared_5171_ = v_isSharedCheck_5176_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_cases_5168_);
                                leanh::lean_dec(v_code_5156_);
                                v___x_5170_ = leanh::lean_box(0);
                                v_isShared_5171_ = v_isSharedCheck_5176_;
                                state = 1;
                                continue;
                            }
                        }
                        5 => {
                            v_fvarId_5177_ = leanh::lean_ctor_get(v_code_5156_, 0);
                            leanh::lean_inc(v_fvarId_5177_);
                            leanh::lean_dec_ref_known(v_code_5156_, 1);
                            v___x_5178_ = l_Lean_Compiler_LCNF_getType(
                                v_fvarId_5177_,
                                v_a_5157_,
                                v_a_5158_,
                                v_a_5159_,
                                v_a_5160_,
                            );
                            return v___x_5178_;
                        }
                        6 => {
                            v_type_5179_ = leanh::lean_ctor_get(v_code_5156_, 0);
                            v_isSharedCheck_5186_ =
                                (!leanh::lean_is_exclusive(v_code_5156_)) as u8;
                            if v_isSharedCheck_5186_ == 0 {
                                v___x_5181_ = v_code_5156_;
                                v_isShared_5182_ = v_isSharedCheck_5186_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_type_5179_);
                                leanh::lean_dec(v_code_5156_);
                                v___x_5181_ = leanh::lean_box(0);
                                v_isShared_5182_ = v_isSharedCheck_5186_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            v_k_5187_ = leanh::lean_ctor_get(v_code_5156_, 1);
                            leanh::lean_inc_ref(v_k_5187_);
                            leanh::lean_dec_ref(v_code_5156_);
                            v_code_5156_ = v_k_5187_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_code_5156_);
                    v___x_5189_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Code_inferType___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Code_inferType___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Code_inferType___closed__1,
                    );
                    v___x_5190_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
                        v___x_5189_,
                        v_a_5157_,
                        v_a_5158_,
                        v_a_5159_,
                        v_a_5160_,
                    );
                    return v___x_5190_;
                }
            }
            1 => {
                v_resultType_5172_ = leanh::lean_ctor_get(v_cases_5168_, 1);
                leanh::lean_inc_ref(v_resultType_5172_);
                leanh::lean_dec_ref(v_cases_5168_);
                if v_isShared_5171_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5170_, 0);
                    leanh::lean_ctor_set(v___x_5170_, 0, v_resultType_5172_);
                    v___x_5174_ = v___x_5170_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_resultType_5172_);
                    v___x_5174_ = v_reuseFailAlloc_5175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5174_;
            }
            3 => {
                if v_isShared_5182_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5181_, 0);
                    v___x_5184_ = v___x_5181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5185_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_type_5179_);
                    v___x_5184_ = v_reuseFailAlloc_5185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_inferType___boxed(
    mut v_pu_5191_: *mut leanh::LeanObject,
    mut v_code_5192_: *mut leanh::LeanObject,
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
    mut v_a_5197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5198_: u8 = 0;
    let mut v_res_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5198_ = (leanh::lean_unbox(v_pu_5191_) as u8);
    v_res_5199_ = l_Lean_Compiler_LCNF_Code_inferType(
        v_pu_boxed_5198_,
        v_code_5192_,
        v_a_5193_,
        v_a_5194_,
        v_a_5195_,
        v_a_5196_,
    );
    leanh::lean_dec(v_a_5196_);
    leanh::lean_dec_ref(v_a_5195_);
    leanh::lean_dec(v_a_5194_);
    leanh::lean_dec_ref(v_a_5193_);
    return v_res_5199_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(
    mut v_pu_5200_: u8,
    mut v_code_5201_: *mut leanh::LeanObject,
    mut v_h__1_5202_: *mut leanh::LeanObject,
    mut v_h__2_5203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_5200_ == 0 {
        let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_5203_);
        v___x_5204_ = leanh::lean_apply_1(v_h__1_5202_, v_code_5201_);
        return v___x_5204_;
    } else {
        let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_5202_);
        v___x_5205_ = leanh::lean_apply_1(v_h__2_5203_, v_code_5201_);
        return v___x_5205_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg___boxed(
    mut v_pu_5206_: *mut leanh::LeanObject,
    mut v_code_5207_: *mut leanh::LeanObject,
    mut v_h__1_5208_: *mut leanh::LeanObject,
    mut v_h__2_5209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_32__boxed_5210_: u8 = 0;
    let mut v_res_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_32__boxed_5210_ = (leanh::lean_unbox(v_pu_5206_) as u8);
    v_res_5211_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___redArg(v_pu_32__boxed_5210_, v_code_5207_, v_h__1_5208_, v_h__2_5209_);
    return v_res_5211_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(
    mut v_motive_5212_: *mut leanh::LeanObject,
    mut v_pu_5213_: u8,
    mut v_code_5214_: *mut leanh::LeanObject,
    mut v_h__1_5215_: *mut leanh::LeanObject,
    mut v_h__2_5216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_5213_ == 0 {
        let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_5216_);
        v___x_5217_ = leanh::lean_apply_1(v_h__1_5215_, v_code_5214_);
        return v___x_5217_;
    } else {
        let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_5215_);
        v___x_5218_ = leanh::lean_apply_1(v_h__2_5216_, v_code_5214_);
        return v___x_5218_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter___boxed(
    mut v_motive_5219_: *mut leanh::LeanObject,
    mut v_pu_5220_: *mut leanh::LeanObject,
    mut v_code_5221_: *mut leanh::LeanObject,
    mut v_h__1_5222_: *mut leanh::LeanObject,
    mut v_h__2_5223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_39__boxed_5224_: u8 = 0;
    let mut v_res_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_39__boxed_5224_ = (leanh::lean_unbox(v_pu_5220_) as u8);
    v_res_5225_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__3_splitter(v_motive_5219_, v_pu_39__boxed_5224_, v_code_5221_, v_h__1_5222_, v_h__2_5223_);
    return v_res_5225_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter___redArg(
    mut v_code_5226_: *mut leanh::LeanObject,
    mut v_h__1_5227_: *mut leanh::LeanObject,
    mut v_h__2_5228_: *mut leanh::LeanObject,
    mut v_h__3_5229_: *mut leanh::LeanObject,
    mut v_h__4_5230_: *mut leanh::LeanObject,
    mut v_h__5_5231_: *mut leanh::LeanObject,
    mut v_h__6_5232_: *mut leanh::LeanObject,
    mut v_h__7_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_code_5226_) {
        0 => {
            let mut v_decl_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5233_);
            leanh::lean_dec(v_h__6_5232_);
            leanh::lean_dec(v_h__5_5231_);
            leanh::lean_dec(v_h__4_5230_);
            leanh::lean_dec(v_h__3_5229_);
            leanh::lean_dec(v_h__2_5228_);
            v_decl_5234_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc_ref(v_decl_5234_);
            v_k_5235_ = leanh::lean_ctor_get(v_code_5226_, 1);
            leanh::lean_inc_ref(v_k_5235_);
            leanh::lean_dec_ref_known(v_code_5226_, 2);
            v___x_5236_ = leanh::lean_apply_2(v_h__1_5227_, v_decl_5234_, v_k_5235_);
            return v___x_5236_;
        }
        1 => {
            let mut v_decl_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5233_);
            leanh::lean_dec(v_h__6_5232_);
            leanh::lean_dec(v_h__5_5231_);
            leanh::lean_dec(v_h__4_5230_);
            leanh::lean_dec(v_h__3_5229_);
            leanh::lean_dec(v_h__1_5227_);
            v_decl_5237_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc_ref(v_decl_5237_);
            v_k_5238_ = leanh::lean_ctor_get(v_code_5226_, 1);
            leanh::lean_inc_ref(v_k_5238_);
            leanh::lean_dec_ref_known(v_code_5226_, 2);
            v___x_5239_ = leanh::lean_apply_3(
                v_h__2_5228_,
                v_decl_5237_,
                v_k_5238_,
                leanh::lean_box(0),
            );
            return v___x_5239_;
        }
        2 => {
            let mut v_decl_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5233_);
            leanh::lean_dec(v_h__6_5232_);
            leanh::lean_dec(v_h__5_5231_);
            leanh::lean_dec(v_h__4_5230_);
            leanh::lean_dec(v_h__2_5228_);
            leanh::lean_dec(v_h__1_5227_);
            v_decl_5240_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc_ref(v_decl_5240_);
            v_k_5241_ = leanh::lean_ctor_get(v_code_5226_, 1);
            leanh::lean_inc_ref(v_k_5241_);
            leanh::lean_dec_ref_known(v_code_5226_, 2);
            v___x_5242_ = leanh::lean_apply_2(v_h__3_5229_, v_decl_5240_, v_k_5241_);
            return v___x_5242_;
        }
        3 => {
            let mut v_fvarId_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5233_);
            leanh::lean_dec(v_h__6_5232_);
            leanh::lean_dec(v_h__4_5230_);
            leanh::lean_dec(v_h__3_5229_);
            leanh::lean_dec(v_h__2_5228_);
            leanh::lean_dec(v_h__1_5227_);
            v_fvarId_5243_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc(v_fvarId_5243_);
            v_args_5244_ = leanh::lean_ctor_get(v_code_5226_, 1);
            leanh::lean_inc_ref(v_args_5244_);
            leanh::lean_dec_ref_known(v_code_5226_, 2);
            v___x_5245_ = leanh::lean_apply_2(v_h__5_5231_, v_fvarId_5243_, v_args_5244_);
            return v___x_5245_;
        }
        4 => {
            let mut v_cases_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_5232_);
            leanh::lean_dec(v_h__5_5231_);
            leanh::lean_dec(v_h__4_5230_);
            leanh::lean_dec(v_h__3_5229_);
            leanh::lean_dec(v_h__2_5228_);
            leanh::lean_dec(v_h__1_5227_);
            v_cases_5246_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc_ref(v_cases_5246_);
            leanh::lean_dec_ref_known(v_code_5226_, 1);
            v___x_5247_ = leanh::lean_apply_1(v_h__7_5233_, v_cases_5246_);
            return v___x_5247_;
        }
        5 => {
            let mut v_fvarId_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5233_);
            leanh::lean_dec(v_h__6_5232_);
            leanh::lean_dec(v_h__5_5231_);
            leanh::lean_dec(v_h__3_5229_);
            leanh::lean_dec(v_h__2_5228_);
            leanh::lean_dec(v_h__1_5227_);
            v_fvarId_5248_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc(v_fvarId_5248_);
            leanh::lean_dec_ref_known(v_code_5226_, 1);
            v___x_5249_ = leanh::lean_apply_1(v_h__4_5230_, v_fvarId_5248_);
            return v___x_5249_;
        }
        _ => {
            let mut v_type_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5233_);
            leanh::lean_dec(v_h__5_5231_);
            leanh::lean_dec(v_h__4_5230_);
            leanh::lean_dec(v_h__3_5229_);
            leanh::lean_dec(v_h__2_5228_);
            leanh::lean_dec(v_h__1_5227_);
            v_type_5250_ = leanh::lean_ctor_get(v_code_5226_, 0);
            leanh::lean_inc_ref(v_type_5250_);
            leanh::lean_dec_ref_known(v_code_5226_, 1);
            v___x_5251_ = leanh::lean_apply_1(v_h__6_5232_, v_type_5250_);
            return v___x_5251_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_Code_inferType_match__1_splitter(
    mut v_motive_5252_: *mut leanh::LeanObject,
    mut v_code_5253_: *mut leanh::LeanObject,
    mut v_h__1_5254_: *mut leanh::LeanObject,
    mut v_h__2_5255_: *mut leanh::LeanObject,
    mut v_h__3_5256_: *mut leanh::LeanObject,
    mut v_h__4_5257_: *mut leanh::LeanObject,
    mut v_h__5_5258_: *mut leanh::LeanObject,
    mut v_h__6_5259_: *mut leanh::LeanObject,
    mut v_h__7_5260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_code_5253_) {
        0 => {
            let mut v_decl_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5260_);
            leanh::lean_dec(v_h__6_5259_);
            leanh::lean_dec(v_h__5_5258_);
            leanh::lean_dec(v_h__4_5257_);
            leanh::lean_dec(v_h__3_5256_);
            leanh::lean_dec(v_h__2_5255_);
            v_decl_5261_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc_ref(v_decl_5261_);
            v_k_5262_ = leanh::lean_ctor_get(v_code_5253_, 1);
            leanh::lean_inc_ref(v_k_5262_);
            leanh::lean_dec_ref_known(v_code_5253_, 2);
            v___x_5263_ = leanh::lean_apply_2(v_h__1_5254_, v_decl_5261_, v_k_5262_);
            return v___x_5263_;
        }
        1 => {
            let mut v_decl_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5260_);
            leanh::lean_dec(v_h__6_5259_);
            leanh::lean_dec(v_h__5_5258_);
            leanh::lean_dec(v_h__4_5257_);
            leanh::lean_dec(v_h__3_5256_);
            leanh::lean_dec(v_h__1_5254_);
            v_decl_5264_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc_ref(v_decl_5264_);
            v_k_5265_ = leanh::lean_ctor_get(v_code_5253_, 1);
            leanh::lean_inc_ref(v_k_5265_);
            leanh::lean_dec_ref_known(v_code_5253_, 2);
            v___x_5266_ = leanh::lean_apply_3(
                v_h__2_5255_,
                v_decl_5264_,
                v_k_5265_,
                leanh::lean_box(0),
            );
            return v___x_5266_;
        }
        2 => {
            let mut v_decl_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5260_);
            leanh::lean_dec(v_h__6_5259_);
            leanh::lean_dec(v_h__5_5258_);
            leanh::lean_dec(v_h__4_5257_);
            leanh::lean_dec(v_h__2_5255_);
            leanh::lean_dec(v_h__1_5254_);
            v_decl_5267_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc_ref(v_decl_5267_);
            v_k_5268_ = leanh::lean_ctor_get(v_code_5253_, 1);
            leanh::lean_inc_ref(v_k_5268_);
            leanh::lean_dec_ref_known(v_code_5253_, 2);
            v___x_5269_ = leanh::lean_apply_2(v_h__3_5256_, v_decl_5267_, v_k_5268_);
            return v___x_5269_;
        }
        3 => {
            let mut v_fvarId_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_args_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5260_);
            leanh::lean_dec(v_h__6_5259_);
            leanh::lean_dec(v_h__4_5257_);
            leanh::lean_dec(v_h__3_5256_);
            leanh::lean_dec(v_h__2_5255_);
            leanh::lean_dec(v_h__1_5254_);
            v_fvarId_5270_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc(v_fvarId_5270_);
            v_args_5271_ = leanh::lean_ctor_get(v_code_5253_, 1);
            leanh::lean_inc_ref(v_args_5271_);
            leanh::lean_dec_ref_known(v_code_5253_, 2);
            v___x_5272_ = leanh::lean_apply_2(v_h__5_5258_, v_fvarId_5270_, v_args_5271_);
            return v___x_5272_;
        }
        4 => {
            let mut v_cases_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_5259_);
            leanh::lean_dec(v_h__5_5258_);
            leanh::lean_dec(v_h__4_5257_);
            leanh::lean_dec(v_h__3_5256_);
            leanh::lean_dec(v_h__2_5255_);
            leanh::lean_dec(v_h__1_5254_);
            v_cases_5273_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc_ref(v_cases_5273_);
            leanh::lean_dec_ref_known(v_code_5253_, 1);
            v___x_5274_ = leanh::lean_apply_1(v_h__7_5260_, v_cases_5273_);
            return v___x_5274_;
        }
        5 => {
            let mut v_fvarId_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5260_);
            leanh::lean_dec(v_h__6_5259_);
            leanh::lean_dec(v_h__5_5258_);
            leanh::lean_dec(v_h__3_5256_);
            leanh::lean_dec(v_h__2_5255_);
            leanh::lean_dec(v_h__1_5254_);
            v_fvarId_5275_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc(v_fvarId_5275_);
            leanh::lean_dec_ref_known(v_code_5253_, 1);
            v___x_5276_ = leanh::lean_apply_1(v_h__4_5257_, v_fvarId_5275_);
            return v___x_5276_;
        }
        _ => {
            let mut v_type_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_5260_);
            leanh::lean_dec(v_h__5_5258_);
            leanh::lean_dec(v_h__4_5257_);
            leanh::lean_dec(v_h__3_5256_);
            leanh::lean_dec(v_h__2_5255_);
            leanh::lean_dec(v_h__1_5254_);
            v_type_5277_ = leanh::lean_ctor_get(v_code_5253_, 0);
            leanh::lean_inc_ref(v_type_5277_);
            leanh::lean_dec_ref_known(v_code_5253_, 1);
            v___x_5278_ = leanh::lean_apply_1(v_h__6_5259_, v_type_5277_);
            return v___x_5278_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_inferParamType(
    mut v_pu_5279_: u8,
    mut v_params_5280_: *mut leanh::LeanObject,
    mut v_code_5281_: *mut leanh::LeanObject,
    mut v_a_5282_: *mut leanh::LeanObject,
    mut v_a_5283_: *mut leanh::LeanObject,
    mut v_a_5284_: *mut leanh::LeanObject,
    mut v_a_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5287_ = l_Lean_Compiler_LCNF_Code_inferType(
        v_pu_5279_,
        v_code_5281_,
        v_a_5282_,
        v_a_5283_,
        v_a_5284_,
        v_a_5285_,
    );
    if leanh::lean_obj_tag(v___x_5287_) == 0 {
        let mut v_a_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_5289_: usize = 0;
        let mut v___x_5290_: usize = 0;
        let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_5288_ = leanh::lean_ctor_get(v___x_5287_, 0);
        leanh::lean_inc(v_a_5288_);
        leanh::lean_dec_ref_known(v___x_5287_, 1);
        v_sz_5289_ = lean_array_size(v_params_5280_);
        v___x_5290_ = 0usize;
        v___x_5291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_InferType_Pure_mkForallParams_spec__0(v_sz_5289_, v___x_5290_, v_params_5280_);
        v___x_5292_ = leanh::lean_unsigned_to_nat(32);
        v___x_5293_ = lean_mk_empty_array_with_capacity(v___x_5292_);
        leanh::lean_dec_ref(v___x_5293_);
        v___x_5294_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4_once
            ),
            _init_l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg___closed__4,
        );
        v___x_5295_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallFVars(
            v___x_5291_,
            v_a_5288_,
            v___x_5294_,
            v_a_5282_,
            v_a_5283_,
            v_a_5284_,
            v_a_5285_,
        );
        leanh::lean_dec(v_a_5288_);
        leanh::lean_dec_ref(v___x_5291_);
        return v___x_5295_;
    } else {
        leanh::lean_dec_ref(v_params_5280_);
        return v___x_5287_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_inferParamType___boxed(
    mut v_pu_5296_: *mut leanh::LeanObject,
    mut v_params_5297_: *mut leanh::LeanObject,
    mut v_code_5298_: *mut leanh::LeanObject,
    mut v_a_5299_: *mut leanh::LeanObject,
    mut v_a_5300_: *mut leanh::LeanObject,
    mut v_a_5301_: *mut leanh::LeanObject,
    mut v_a_5302_: *mut leanh::LeanObject,
    mut v_a_5303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5304_: u8 = 0;
    let mut v_res_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5304_ = (leanh::lean_unbox(v_pu_5296_) as u8);
    v_res_5305_ = l_Lean_Compiler_LCNF_Code_inferParamType(
        v_pu_boxed_5304_,
        v_params_5297_,
        v_code_5298_,
        v_a_5299_,
        v_a_5300_,
        v_a_5301_,
        v_a_5302_,
    );
    leanh::lean_dec(v_a_5302_);
    leanh::lean_dec_ref(v_a_5301_);
    leanh::lean_dec(v_a_5300_);
    leanh::lean_dec_ref(v_a_5299_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_inferType(
    mut v_pu_5306_: u8,
    mut v_alt_5307_: *mut leanh::LeanObject,
    mut v_a_5308_: *mut leanh::LeanObject,
    mut v_a_5309_: *mut leanh::LeanObject,
    mut v_a_5310_: *mut leanh::LeanObject,
    mut v_a_5311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_alt_5307_) {
        0 => {
            let mut v_code_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_code_5313_ = leanh::lean_ctor_get(v_alt_5307_, 2);
            leanh::lean_inc_ref(v_code_5313_);
            leanh::lean_dec_ref_known(v_alt_5307_, 3);
            v___x_5314_ = l_Lean_Compiler_LCNF_Code_inferType(
                v_pu_5306_,
                v_code_5313_,
                v_a_5308_,
                v_a_5309_,
                v_a_5310_,
                v_a_5311_,
            );
            return v___x_5314_;
        }
        1 => {
            let mut v_code_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_code_5315_ = leanh::lean_ctor_get(v_alt_5307_, 1);
            leanh::lean_inc_ref(v_code_5315_);
            leanh::lean_dec_ref_known(v_alt_5307_, 2);
            v___x_5316_ = l_Lean_Compiler_LCNF_Code_inferType(
                v_pu_5306_,
                v_code_5315_,
                v_a_5308_,
                v_a_5309_,
                v_a_5310_,
                v_a_5311_,
            );
            return v___x_5316_;
        }
        _ => {
            let mut v_code_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_code_5317_ = leanh::lean_ctor_get(v_alt_5307_, 0);
            leanh::lean_inc_ref(v_code_5317_);
            leanh::lean_dec_ref_known(v_alt_5307_, 1);
            v___x_5318_ = l_Lean_Compiler_LCNF_Code_inferType(
                v_pu_5306_,
                v_code_5317_,
                v_a_5308_,
                v_a_5309_,
                v_a_5310_,
                v_a_5311_,
            );
            return v___x_5318_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_inferType___boxed(
    mut v_pu_5319_: *mut leanh::LeanObject,
    mut v_alt_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
    mut v_a_5322_: *mut leanh::LeanObject,
    mut v_a_5323_: *mut leanh::LeanObject,
    mut v_a_5324_: *mut leanh::LeanObject,
    mut v_a_5325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5326_: u8 = 0;
    let mut v_res_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5326_ = (leanh::lean_unbox(v_pu_5319_) as u8);
    v_res_5327_ = l_Lean_Compiler_LCNF_Alt_inferType(
        v_pu_boxed_5326_,
        v_alt_5320_,
        v_a_5321_,
        v_a_5322_,
        v_a_5323_,
        v_a_5324_,
    );
    leanh::lean_dec(v_a_5324_);
    leanh::lean_dec_ref(v_a_5323_);
    leanh::lean_dec(v_a_5322_);
    leanh::lean_dec_ref(v_a_5321_);
    return v_res_5327_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxLetDecl(
    mut v_pu_5328_: u8,
    mut v_e_5329_: *mut leanh::LeanObject,
    mut v_prefixName_5330_: *mut leanh::LeanObject,
    mut v_a_5331_: *mut leanh::LeanObject,
    mut v_a_5332_: *mut leanh::LeanObject,
    mut v_a_5333_: *mut leanh::LeanObject,
    mut v_a_5334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5344_: u8 = 0;
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5348_: u8 = 0;
    let mut v_a_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5336_ =
                    l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v_prefixName_5330_, v_a_5332_);
                if leanh::lean_obj_tag(v___x_5336_) == 0 {
                    v_a_5337_ = leanh::lean_ctor_get(v___x_5336_, 0);
                    leanh::lean_inc(v_a_5337_);
                    leanh::lean_dec_ref_known(v___x_5336_, 1);
                    leanh::lean_inc(v_e_5329_);
                    v___x_5338_ = l_Lean_Compiler_LCNF_LetValue_inferType(
                        v_pu_5328_, v_e_5329_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_,
                    );
                    if leanh::lean_obj_tag(v___x_5338_) == 0 {
                        v_a_5339_ = leanh::lean_ctor_get(v___x_5338_, 0);
                        leanh::lean_inc(v_a_5339_);
                        leanh::lean_dec_ref_known(v___x_5338_, 1);
                        v___x_5340_ = l_Lean_Compiler_LCNF_mkLetDecl(
                            v_pu_5328_, v_a_5337_, v_a_5339_, v_e_5329_, v_a_5331_, v_a_5332_,
                            v_a_5333_, v_a_5334_,
                        );
                        return v___x_5340_;
                    } else {
                        leanh::lean_dec(v_a_5337_);
                        leanh::lean_dec(v_e_5329_);
                        v_a_5341_ = leanh::lean_ctor_get(v___x_5338_, 0);
                        v_isSharedCheck_5348_ =
                            (!leanh::lean_is_exclusive(v___x_5338_)) as u8;
                        if v_isSharedCheck_5348_ == 0 {
                            v___x_5343_ = v___x_5338_;
                            v_isShared_5344_ = v_isSharedCheck_5348_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5341_);
                            leanh::lean_dec(v___x_5338_);
                            v___x_5343_ = leanh::lean_box(0);
                            v_isShared_5344_ = v_isSharedCheck_5348_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_e_5329_);
                    v_a_5349_ = leanh::lean_ctor_get(v___x_5336_, 0);
                    v_isSharedCheck_5356_ = (!leanh::lean_is_exclusive(v___x_5336_)) as u8;
                    if v_isSharedCheck_5356_ == 0 {
                        v___x_5351_ = v___x_5336_;
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5349_);
                        leanh::lean_dec(v___x_5336_);
                        v___x_5351_ = leanh::lean_box(0);
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5344_ == 0 {
                    v___x_5346_ = v___x_5343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
                    v___x_5346_ = v_reuseFailAlloc_5347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5346_;
            }
            3 => {
                if v_isShared_5352_ == 0 {
                    v___x_5354_ = v___x_5351_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
                    v___x_5354_ = v_reuseFailAlloc_5355_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxLetDecl___boxed(
    mut v_pu_5357_: *mut leanh::LeanObject,
    mut v_e_5358_: *mut leanh::LeanObject,
    mut v_prefixName_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5365_: u8 = 0;
    let mut v_res_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5365_ = (leanh::lean_unbox(v_pu_5357_) as u8);
    v_res_5366_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
        v_pu_boxed_5365_,
        v_e_5358_,
        v_prefixName_5359_,
        v_a_5360_,
        v_a_5361_,
        v_a_5362_,
        v_a_5363_,
    );
    leanh::lean_dec(v_a_5363_);
    leanh::lean_dec_ref(v_a_5362_);
    leanh::lean_dec(v_a_5361_);
    leanh::lean_dec_ref(v_a_5360_);
    return v_res_5366_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5368_ = l_Lean_Compiler_LCNF_inferAppType___closed__1;
    v___x_5369_ = leanh::lean_unsigned_to_nat(15);
    v___x_5370_ = leanh::lean_unsigned_to_nat(295);
    v___x_5371_ = l_Lean_Compiler_LCNF_mkForallParams___closed__0;
    v___x_5372_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_5373_ = l_mkPanicMessageWithDecl(
        v___x_5372_,
        v___x_5371_,
        v___x_5370_,
        v___x_5369_,
        v___x_5368_,
    );
    return v___x_5373_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkForallParams(
    mut v_pu_5374_: u8,
    mut v_params_5375_: *mut leanh::LeanObject,
    mut v_type_5376_: *mut leanh::LeanObject,
    mut v_a_5377_: *mut leanh::LeanObject,
    mut v_a_5378_: *mut leanh::LeanObject,
    mut v_a_5379_: *mut leanh::LeanObject,
    mut v_a_5380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_pu_5374_ == 0 {
        let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5382_ = l_Lean_Compiler_LCNF_InferType_Pure_mkForallParams___redArg(
            v_params_5375_,
            v_type_5376_,
            v_a_5377_,
            v_a_5378_,
            v_a_5379_,
            v_a_5380_,
        );
        return v___x_5382_;
    } else {
        let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_params_5375_);
        v___x_5383_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkForallParams___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkForallParams___closed__1_once),
            _init_l_Lean_Compiler_LCNF_mkForallParams___closed__1,
        );
        v___x_5384_ = l_panic___at___00Lean_Compiler_LCNF_inferAppType_spec__0(
            v___x_5383_,
            v_a_5377_,
            v_a_5378_,
            v_a_5379_,
            v_a_5380_,
        );
        return v___x_5384_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkForallParams___boxed(
    mut v_pu_5385_: *mut leanh::LeanObject,
    mut v_params_5386_: *mut leanh::LeanObject,
    mut v_type_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
    mut v_a_5389_: *mut leanh::LeanObject,
    mut v_a_5390_: *mut leanh::LeanObject,
    mut v_a_5391_: *mut leanh::LeanObject,
    mut v_a_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5393_: u8 = 0;
    let mut v_res_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5393_ = (leanh::lean_unbox(v_pu_5385_) as u8);
    v_res_5394_ = l_Lean_Compiler_LCNF_mkForallParams(
        v_pu_boxed_5393_,
        v_params_5386_,
        v_type_5387_,
        v_a_5388_,
        v_a_5389_,
        v_a_5390_,
        v_a_5391_,
    );
    leanh::lean_dec(v_a_5391_);
    leanh::lean_dec_ref(v_a_5390_);
    leanh::lean_dec(v_a_5389_);
    leanh::lean_dec_ref(v_a_5388_);
    leanh::lean_dec_ref(v_type_5387_);
    return v_res_5394_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(
    mut v_pu_5395_: u8,
    mut v_params_5396_: *mut leanh::LeanObject,
    mut v_code_5397_: *mut leanh::LeanObject,
    mut v_prefixName_5398_: *mut leanh::LeanObject,
    mut v_a_5399_: *mut leanh::LeanObject,
    mut v_a_5400_: *mut leanh::LeanObject,
    mut v_a_5401_: *mut leanh::LeanObject,
    mut v_a_5402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5414_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5418_: u8 = 0;
    let mut v_a_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5422_: u8 = 0;
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut v_a_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5430_: u8 = 0;
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_code_5397_);
                v___x_5404_ = l_Lean_Compiler_LCNF_Code_inferType(
                    v_pu_5395_,
                    v_code_5397_,
                    v_a_5399_,
                    v_a_5400_,
                    v_a_5401_,
                    v_a_5402_,
                );
                if leanh::lean_obj_tag(v___x_5404_) == 0 {
                    v_a_5405_ = leanh::lean_ctor_get(v___x_5404_, 0);
                    leanh::lean_inc(v_a_5405_);
                    leanh::lean_dec_ref_known(v___x_5404_, 1);
                    leanh::lean_inc_ref(v_params_5396_);
                    v___x_5406_ = l_Lean_Compiler_LCNF_mkForallParams(
                        v_pu_5395_,
                        v_params_5396_,
                        v_a_5405_,
                        v_a_5399_,
                        v_a_5400_,
                        v_a_5401_,
                        v_a_5402_,
                    );
                    leanh::lean_dec(v_a_5405_);
                    if leanh::lean_obj_tag(v___x_5406_) == 0 {
                        v_a_5407_ = leanh::lean_ctor_get(v___x_5406_, 0);
                        leanh::lean_inc(v_a_5407_);
                        leanh::lean_dec_ref_known(v___x_5406_, 1);
                        v___x_5408_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(
                            v_prefixName_5398_,
                            v_a_5400_,
                        );
                        if leanh::lean_obj_tag(v___x_5408_) == 0 {
                            v_a_5409_ = leanh::lean_ctor_get(v___x_5408_, 0);
                            leanh::lean_inc(v_a_5409_);
                            leanh::lean_dec_ref_known(v___x_5408_, 1);
                            v___x_5410_ = l_Lean_Compiler_LCNF_mkFunDecl(
                                v_pu_5395_,
                                v_a_5409_,
                                v_a_5407_,
                                v_params_5396_,
                                v_code_5397_,
                                v_a_5399_,
                                v_a_5400_,
                                v_a_5401_,
                                v_a_5402_,
                            );
                            return v___x_5410_;
                        } else {
                            leanh::lean_dec(v_a_5407_);
                            leanh::lean_dec_ref(v_code_5397_);
                            leanh::lean_dec_ref(v_params_5396_);
                            v_a_5411_ = leanh::lean_ctor_get(v___x_5408_, 0);
                            v_isSharedCheck_5418_ =
                                (!leanh::lean_is_exclusive(v___x_5408_)) as u8;
                            if v_isSharedCheck_5418_ == 0 {
                                v___x_5413_ = v___x_5408_;
                                v_isShared_5414_ = v_isSharedCheck_5418_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5411_);
                                leanh::lean_dec(v___x_5408_);
                                v___x_5413_ = leanh::lean_box(0);
                                v_isShared_5414_ = v_isSharedCheck_5418_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_prefixName_5398_);
                        leanh::lean_dec_ref(v_code_5397_);
                        leanh::lean_dec_ref(v_params_5396_);
                        v_a_5419_ = leanh::lean_ctor_get(v___x_5406_, 0);
                        v_isSharedCheck_5426_ =
                            (!leanh::lean_is_exclusive(v___x_5406_)) as u8;
                        if v_isSharedCheck_5426_ == 0 {
                            v___x_5421_ = v___x_5406_;
                            v_isShared_5422_ = v_isSharedCheck_5426_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5419_);
                            leanh::lean_dec(v___x_5406_);
                            v___x_5421_ = leanh::lean_box(0);
                            v_isShared_5422_ = v_isSharedCheck_5426_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_prefixName_5398_);
                    leanh::lean_dec_ref(v_code_5397_);
                    leanh::lean_dec_ref(v_params_5396_);
                    v_a_5427_ = leanh::lean_ctor_get(v___x_5404_, 0);
                    v_isSharedCheck_5434_ = (!leanh::lean_is_exclusive(v___x_5404_)) as u8;
                    if v_isSharedCheck_5434_ == 0 {
                        v___x_5429_ = v___x_5404_;
                        v_isShared_5430_ = v_isSharedCheck_5434_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5427_);
                        leanh::lean_dec(v___x_5404_);
                        v___x_5429_ = leanh::lean_box(0);
                        v_isShared_5430_ = v_isSharedCheck_5434_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5414_ == 0 {
                    v___x_5416_ = v___x_5413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_a_5411_);
                    v___x_5416_ = v_reuseFailAlloc_5417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5416_;
            }
            3 => {
                if v_isShared_5422_ == 0 {
                    v___x_5424_ = v___x_5421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5419_);
                    v___x_5424_ = v_reuseFailAlloc_5425_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5424_;
            }
            5 => {
                if v_isShared_5430_ == 0 {
                    v___x_5432_ = v___x_5429_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_a_5427_);
                    v___x_5432_ = v_reuseFailAlloc_5433_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux___boxed(
    mut v_pu_5435_: *mut leanh::LeanObject,
    mut v_params_5436_: *mut leanh::LeanObject,
    mut v_code_5437_: *mut leanh::LeanObject,
    mut v_prefixName_5438_: *mut leanh::LeanObject,
    mut v_a_5439_: *mut leanh::LeanObject,
    mut v_a_5440_: *mut leanh::LeanObject,
    mut v_a_5441_: *mut leanh::LeanObject,
    mut v_a_5442_: *mut leanh::LeanObject,
    mut v_a_5443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5444_: u8 = 0;
    let mut v_res_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5444_ = (leanh::lean_unbox(v_pu_5435_) as u8);
    v_res_5445_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(
        v_pu_boxed_5444_,
        v_params_5436_,
        v_code_5437_,
        v_prefixName_5438_,
        v_a_5439_,
        v_a_5440_,
        v_a_5441_,
        v_a_5442_,
    );
    leanh::lean_dec(v_a_5442_);
    leanh::lean_dec_ref(v_a_5441_);
    leanh::lean_dec(v_a_5440_);
    leanh::lean_dec_ref(v_a_5439_);
    return v_res_5445_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxFunDecl(
    mut v_params_5446_: *mut leanh::LeanObject,
    mut v_code_5447_: *mut leanh::LeanObject,
    mut v_prefixName_5448_: *mut leanh::LeanObject,
    mut v_a_5449_: *mut leanh::LeanObject,
    mut v_a_5450_: *mut leanh::LeanObject,
    mut v_a_5451_: *mut leanh::LeanObject,
    mut v_a_5452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5454_: u8 = 0;
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5454_ = 0;
    v___x_5455_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(
        v___x_5454_,
        v_params_5446_,
        v_code_5447_,
        v_prefixName_5448_,
        v_a_5449_,
        v_a_5450_,
        v_a_5451_,
        v_a_5452_,
    );
    return v___x_5455_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(
    mut v_params_5456_: *mut leanh::LeanObject,
    mut v_code_5457_: *mut leanh::LeanObject,
    mut v_prefixName_5458_: *mut leanh::LeanObject,
    mut v_a_5459_: *mut leanh::LeanObject,
    mut v_a_5460_: *mut leanh::LeanObject,
    mut v_a_5461_: *mut leanh::LeanObject,
    mut v_a_5462_: *mut leanh::LeanObject,
    mut v_a_5463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5464_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(
        v_params_5456_,
        v_code_5457_,
        v_prefixName_5458_,
        v_a_5459_,
        v_a_5460_,
        v_a_5461_,
        v_a_5462_,
    );
    leanh::lean_dec(v_a_5462_);
    leanh::lean_dec_ref(v_a_5461_);
    leanh::lean_dec(v_a_5460_);
    leanh::lean_dec_ref(v_a_5459_);
    return v_res_5464_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxJpDecl(
    mut v_pu_5465_: u8,
    mut v_params_5466_: *mut leanh::LeanObject,
    mut v_code_5467_: *mut leanh::LeanObject,
    mut v_prefixName_5468_: *mut leanh::LeanObject,
    mut v_a_5469_: *mut leanh::LeanObject,
    mut v_a_5470_: *mut leanh::LeanObject,
    mut v_a_5471_: *mut leanh::LeanObject,
    mut v_a_5472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5474_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(
        v_pu_5465_,
        v_params_5466_,
        v_code_5467_,
        v_prefixName_5468_,
        v_a_5469_,
        v_a_5470_,
        v_a_5471_,
        v_a_5472_,
    );
    return v___x_5474_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(
    mut v_pu_5475_: *mut leanh::LeanObject,
    mut v_params_5476_: *mut leanh::LeanObject,
    mut v_code_5477_: *mut leanh::LeanObject,
    mut v_prefixName_5478_: *mut leanh::LeanObject,
    mut v_a_5479_: *mut leanh::LeanObject,
    mut v_a_5480_: *mut leanh::LeanObject,
    mut v_a_5481_: *mut leanh::LeanObject,
    mut v_a_5482_: *mut leanh::LeanObject,
    mut v_a_5483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5484_: u8 = 0;
    let mut v_res_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5484_ = (leanh::lean_unbox(v_pu_5475_) as u8);
    v_res_5485_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(
        v_pu_boxed_5484_,
        v_params_5476_,
        v_code_5477_,
        v_prefixName_5478_,
        v_a_5479_,
        v_a_5480_,
        v_a_5481_,
        v_a_5482_,
    );
    leanh::lean_dec(v_a_5482_);
    leanh::lean_dec_ref(v_a_5481_);
    leanh::lean_dec(v_a_5480_);
    leanh::lean_dec_ref(v_a_5479_);
    return v_res_5485_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(
    mut v_pu_5486_: u8,
    mut v_param_5487_: *mut leanh::LeanObject,
    mut v_code_5488_: *mut leanh::LeanObject,
    mut v_prefixName_5489_: *mut leanh::LeanObject,
    mut v_a_5490_: *mut leanh::LeanObject,
    mut v_a_5491_: *mut leanh::LeanObject,
    mut v_a_5492_: *mut leanh::LeanObject,
    mut v_a_5493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5495_ = leanh::lean_unsigned_to_nat(1);
    v___x_5496_ = lean_mk_empty_array_with_capacity(v___x_5495_);
    v_params_5497_ = lean_array_push(v___x_5496_, v_param_5487_);
    v___x_5498_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_mkAuxFunDeclAux(
        v_pu_5486_,
        v_params_5497_,
        v_code_5488_,
        v_prefixName_5489_,
        v_a_5490_,
        v_a_5491_,
        v_a_5492_,
        v_a_5493_,
    );
    return v___x_5498_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(
    mut v_pu_5499_: *mut leanh::LeanObject,
    mut v_param_5500_: *mut leanh::LeanObject,
    mut v_code_5501_: *mut leanh::LeanObject,
    mut v_prefixName_5502_: *mut leanh::LeanObject,
    mut v_a_5503_: *mut leanh::LeanObject,
    mut v_a_5504_: *mut leanh::LeanObject,
    mut v_a_5505_: *mut leanh::LeanObject,
    mut v_a_5506_: *mut leanh::LeanObject,
    mut v_a_5507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5508_: u8 = 0;
    let mut v_res_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5508_ = (leanh::lean_unbox(v_pu_5499_) as u8);
    v_res_5509_ = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(
        v_pu_boxed_5508_,
        v_param_5500_,
        v_code_5501_,
        v_prefixName_5502_,
        v_a_5503_,
        v_a_5504_,
        v_a_5505_,
        v_a_5506_,
    );
    leanh::lean_dec(v_a_5506_);
    leanh::lean_dec_ref(v_a_5505_);
    leanh::lean_dec(v_a_5504_);
    leanh::lean_dec_ref(v_a_5503_);
    return v_res_5509_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(
    mut v_msg_5510_: *mut leanh::LeanObject,
    mut v___y_5511_: *mut leanh::LeanObject,
    mut v___y_5512_: *mut leanh::LeanObject,
    mut v___y_5513_: *mut leanh::LeanObject,
    mut v___y_5514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v_env_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5529_: u8 = 0;
    let mut v___x_5530_: u8 = 0;
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5541_: u8 = 0;
    let mut v_unused_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5543_: u8 = 0;
    let mut v_a_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5516_ = leanh::lean_ctor_get(v___y_5513_, 2);
                v_ref_5517_ = leanh::lean_ctor_get(v___y_5513_, 5);
                v___x_5518_ = lean_st_ref_get(v___y_5514_);
                v___x_5519_ = lean_st_ref_get(v___y_5512_);
                v___x_5520_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_5511_);
                if leanh::lean_obj_tag(v___x_5520_) == 0 {
                    v_a_5521_ = leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5543_ = (!leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5543_ == 0 {
                        v___x_5523_ = v___x_5520_;
                        v_isShared_5524_ = v_isSharedCheck_5543_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5521_);
                        leanh::lean_dec(v___x_5520_);
                        v___x_5523_ = leanh::lean_box(0);
                        v_isShared_5524_ = v_isSharedCheck_5543_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5519_);
                    leanh::lean_dec(v___x_5518_);
                    leanh::lean_dec_ref(v_msg_5510_);
                    v_a_5544_ = leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5551_ = (!leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5551_ == 0 {
                        v___x_5546_ = v___x_5520_;
                        v_isShared_5547_ = v_isSharedCheck_5551_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5544_);
                        leanh::lean_dec(v___x_5520_);
                        v___x_5546_ = leanh::lean_box(0);
                        v_isShared_5547_ = v_isSharedCheck_5551_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_5525_ = leanh::lean_ctor_get(v___x_5518_, 0);
                leanh::lean_inc_ref(v_env_5525_);
                leanh::lean_dec(v___x_5518_);
                v_lctx_5526_ = leanh::lean_ctor_get(v___x_5519_, 0);
                v_isSharedCheck_5541_ = (!leanh::lean_is_exclusive(v___x_5519_)) as u8;
                if v_isSharedCheck_5541_ == 0 {
                    v_unused_5542_ = leanh::lean_ctor_get(v___x_5519_, 1);
                    leanh::lean_dec(v_unused_5542_);
                    v___x_5528_ = v___x_5519_;
                    v_isShared_5529_ = v_isSharedCheck_5541_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lctx_5526_);
                    leanh::lean_dec(v___x_5519_);
                    v___x_5528_ = leanh::lean_box(0);
                    v_isShared_5529_ = v_isSharedCheck_5541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5530_ = (leanh::lean_unbox(v_a_5521_) as u8);
                leanh::lean_dec(v_a_5521_);
                v___x_5531_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_5526_, v___x_5530_);
                leanh::lean_dec_ref(v_lctx_5526_);
                v___x_5532_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_InferType_Pure_inferProjType_spec__0___redArg___closed__2);
                leanh::lean_inc_ref(v_options_5516_);
                v___x_5533_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_5533_, 0, v_env_5525_);
                leanh::lean_ctor_set(v___x_5533_, 1, v___x_5532_);
                leanh::lean_ctor_set(v___x_5533_, 2, v___x_5531_);
                leanh::lean_ctor_set(v___x_5533_, 3, v_options_5516_);
                if v_isShared_5529_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5528_, 3);
                    leanh::lean_ctor_set(v___x_5528_, 1, v_msg_5510_);
                    leanh::lean_ctor_set(v___x_5528_, 0, v___x_5533_);
                    v___x_5535_ = v___x_5528_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5540_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5540_, 1, v_msg_5510_);
                    v___x_5535_ = v_reuseFailAlloc_5540_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_ref_5517_);
                v___x_5536_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5536_, 0, v_ref_5517_);
                leanh::lean_ctor_set(v___x_5536_, 1, v___x_5535_);
                if v_isShared_5524_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5523_, 1);
                    leanh::lean_ctor_set(v___x_5523_, 0, v___x_5536_);
                    v___x_5538_ = v___x_5523_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
                    v___x_5538_ = v_reuseFailAlloc_5539_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5538_;
            }
            5 => {
                if v_isShared_5547_ == 0 {
                    v___x_5549_ = v___x_5546_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
                    v___x_5549_ = v_reuseFailAlloc_5550_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg___boxed(
    mut v_msg_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
    mut v___y_5554_: *mut leanh::LeanObject,
    mut v___y_5555_: *mut leanh::LeanObject,
    mut v___y_5556_: *mut leanh::LeanObject,
    mut v___y_5557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5558_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(
        v_msg_5552_,
        v___y_5553_,
        v___y_5554_,
        v___y_5555_,
        v___y_5556_,
    );
    leanh::lean_dec(v___y_5556_);
    leanh::lean_dec_ref(v___y_5555_);
    leanh::lean_dec(v___y_5554_);
    leanh::lean_dec_ref(v___y_5553_);
    return v_res_5558_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(
    mut v_00_u03b1_5559_: *mut leanh::LeanObject,
    mut v_msg_5560_: *mut leanh::LeanObject,
    mut v___y_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5566_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(
        v_msg_5560_,
        v___y_5561_,
        v___y_5562_,
        v___y_5563_,
        v___y_5564_,
    );
    return v___x_5566_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___boxed(
    mut v_00_u03b1_5567_: *mut leanh::LeanObject,
    mut v_msg_5568_: *mut leanh::LeanObject,
    mut v___y_5569_: *mut leanh::LeanObject,
    mut v___y_5570_: *mut leanh::LeanObject,
    mut v___y_5571_: *mut leanh::LeanObject,
    mut v___y_5572_: *mut leanh::LeanObject,
    mut v___y_5573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5574_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1(
        v_00_u03b1_5567_,
        v_msg_5568_,
        v___y_5569_,
        v___y_5570_,
        v___y_5571_,
        v___y_5572_,
    );
    leanh::lean_dec(v___y_5572_);
    leanh::lean_dec_ref(v___y_5571_);
    leanh::lean_dec(v___y_5570_);
    leanh::lean_dec_ref(v___y_5569_);
    return v_res_5574_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(
    mut v_pu_5575_: u8,
    mut v_a_5576_: *mut leanh::LeanObject,
    mut v_b_5577_: *mut leanh::LeanObject,
    mut v___y_5578_: *mut leanh::LeanObject,
    mut v___y_5579_: *mut leanh::LeanObject,
    mut v___y_5580_: *mut leanh::LeanObject,
    mut v___y_5581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5588_: u8 = 0;
    let mut v___x_5589_: u8 = 0;
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5583_ = leanh::lean_ctor_get(v_a_5576_, 0);
                v_start_5584_ = leanh::lean_ctor_get(v_a_5576_, 1);
                v_stop_5585_ = leanh::lean_ctor_get(v_a_5576_, 2);
                v_isSharedCheck_5601_ = (!leanh::lean_is_exclusive(v_a_5576_)) as u8;
                if v_isSharedCheck_5601_ == 0 {
                    v___x_5587_ = v_a_5576_;
                    v_isShared_5588_ = v_isSharedCheck_5601_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_5585_);
                    leanh::lean_inc(v_start_5584_);
                    leanh::lean_inc(v_array_5583_);
                    leanh::lean_dec(v_a_5576_);
                    v___x_5587_ = leanh::lean_box(0);
                    v_isShared_5588_ = v_isSharedCheck_5601_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5589_ = lean_nat_dec_lt(v_start_5584_, v_stop_5585_);
                if v___x_5589_ == 0 {
                    leanh::lean_del_object(v___x_5587_);
                    leanh::lean_dec(v_stop_5585_);
                    leanh::lean_dec(v_start_5584_);
                    leanh::lean_dec_ref(v_array_5583_);
                    v___x_5590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5590_, 0, v_b_5577_);
                    return v___x_5590_;
                } else {
                    v___x_5591_ = lean_array_fget_borrowed(v_array_5583_, v_start_5584_);
                    leanh::lean_inc(v___x_5591_);
                    v___x_5592_ = l_Lean_Compiler_LCNF_Alt_inferType(
                        v_pu_5575_,
                        v___x_5591_,
                        v___y_5578_,
                        v___y_5579_,
                        v___y_5580_,
                        v___y_5581_,
                    );
                    if leanh::lean_obj_tag(v___x_5592_) == 0 {
                        v_a_5593_ = leanh::lean_ctor_get(v___x_5592_, 0);
                        leanh::lean_inc(v_a_5593_);
                        leanh::lean_dec_ref_known(v___x_5592_, 1);
                        v___x_5594_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5595_ = lean_nat_add(v_start_5584_, v___x_5594_);
                        leanh::lean_dec(v_start_5584_);
                        if v_isShared_5588_ == 0 {
                            leanh::lean_ctor_set(v___x_5587_, 1, v___x_5595_);
                            v___x_5597_ = v___x_5587_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5600_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_array_5583_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 1, v___x_5595_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5600_, 2, v_stop_5585_);
                            v___x_5597_ = v_reuseFailAlloc_5600_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5587_);
                        leanh::lean_dec(v_stop_5585_);
                        leanh::lean_dec(v_start_5584_);
                        leanh::lean_dec_ref(v_array_5583_);
                        leanh::lean_dec_ref(v_b_5577_);
                        return v___x_5592_;
                    }
                }
            }
            2 => {
                v___x_5598_ = l_Lean_Compiler_LCNF_joinTypes(v_b_5577_, v_a_5593_);
                v_a_5576_ = v___x_5597_;
                v_b_5577_ = v___x_5598_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(
    mut v_pu_5602_: *mut leanh::LeanObject,
    mut v_a_5603_: *mut leanh::LeanObject,
    mut v_b_5604_: *mut leanh::LeanObject,
    mut v___y_5605_: *mut leanh::LeanObject,
    mut v___y_5606_: *mut leanh::LeanObject,
    mut v___y_5607_: *mut leanh::LeanObject,
    mut v___y_5608_: *mut leanh::LeanObject,
    mut v___y_5609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5610_: u8 = 0;
    let mut v_res_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5610_ = (leanh::lean_unbox(v_pu_5602_) as u8);
    v_res_5611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_boxed_5610_, v_a_5603_, v_b_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
    leanh::lean_dec(v___y_5608_);
    leanh::lean_dec_ref(v___y_5607_);
    leanh::lean_dec(v___y_5606_);
    leanh::lean_dec_ref(v___y_5605_);
    return v_res_5611_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5613_ = l_Lean_Compiler_LCNF_mkCasesResultType___closed__0;
    v___x_5614_ = l_Lean_stringToMessageData(v___x_5613_);
    return v___x_5614_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkCasesResultType(
    mut v_pu_5615_: u8,
    mut v_alts_5616_: *mut leanh::LeanObject,
    mut v_a_5617_: *mut leanh::LeanObject,
    mut v_a_5618_: *mut leanh::LeanObject,
    mut v_a_5619_: *mut leanh::LeanObject,
    mut v_a_5620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: u8 = 0;
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5622_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v_pu_5615_);
                v___x_5636_ = lean_array_get_size(v_alts_5616_);
                v___x_5637_ = leanh::lean_unsigned_to_nat(0);
                v___x_5638_ = lean_nat_dec_eq(v___x_5636_, v___x_5637_);
                if v___x_5638_ == 0 {
                    v___y_5624_ = v_a_5617_;
                    v___y_5625_ = v_a_5618_;
                    v___y_5626_ = v_a_5619_;
                    v___y_5627_ = v_a_5620_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_5622_);
                    leanh::lean_dec_ref(v_alts_5616_);
                    v___x_5639_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_mkCasesResultType___closed__1_once
                        ),
                        _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1,
                    );
                    v___x_5640_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__1___redArg(v___x_5639_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_);
                    v_a_5641_ = leanh::lean_ctor_get(v___x_5640_, 0);
                    v_isSharedCheck_5648_ = (!leanh::lean_is_exclusive(v___x_5640_)) as u8;
                    if v_isSharedCheck_5648_ == 0 {
                        v___x_5643_ = v___x_5640_;
                        v_isShared_5644_ = v_isSharedCheck_5648_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5641_);
                        leanh::lean_dec(v___x_5640_);
                        v___x_5643_ = leanh::lean_box(0);
                        v_isShared_5644_ = v_isSharedCheck_5648_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5628_ = leanh::lean_unsigned_to_nat(0);
                v___x_5629_ = lean_array_get(v___x_5622_, v_alts_5616_, v___x_5628_);
                leanh::lean_dec_ref(v___x_5622_);
                v___x_5630_ = l_Lean_Compiler_LCNF_Alt_inferType(
                    v_pu_5615_,
                    v___x_5629_,
                    v___y_5624_,
                    v___y_5625_,
                    v___y_5626_,
                    v___y_5627_,
                );
                if leanh::lean_obj_tag(v___x_5630_) == 0 {
                    v_a_5631_ = leanh::lean_ctor_get(v___x_5630_, 0);
                    leanh::lean_inc(v_a_5631_);
                    leanh::lean_dec_ref_known(v___x_5630_, 1);
                    v___x_5632_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5633_ = lean_array_get_size(v_alts_5616_);
                    v___x_5634_ =
                        l_Array_toSubarray___redArg(v_alts_5616_, v___x_5632_, v___x_5633_);
                    v___x_5635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_5615_, v___x_5634_, v_a_5631_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_);
                    return v___x_5635_;
                } else {
                    leanh::lean_dec_ref(v_alts_5616_);
                    return v___x_5630_;
                }
            }
            2 => {
                if v_isShared_5644_ == 0 {
                    v___x_5646_ = v___x_5643_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5647_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5641_);
                    v___x_5646_ = v_reuseFailAlloc_5647_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_mkCasesResultType___boxed(
    mut v_pu_5649_: *mut leanh::LeanObject,
    mut v_alts_5650_: *mut leanh::LeanObject,
    mut v_a_5651_: *mut leanh::LeanObject,
    mut v_a_5652_: *mut leanh::LeanObject,
    mut v_a_5653_: *mut leanh::LeanObject,
    mut v_a_5654_: *mut leanh::LeanObject,
    mut v_a_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5656_: u8 = 0;
    let mut v_res_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5656_ = (leanh::lean_unbox(v_pu_5649_) as u8);
    v_res_5657_ = l_Lean_Compiler_LCNF_mkCasesResultType(
        v_pu_boxed_5656_,
        v_alts_5650_,
        v_a_5651_,
        v_a_5652_,
        v_a_5653_,
        v_a_5654_,
    );
    leanh::lean_dec(v_a_5654_);
    leanh::lean_dec_ref(v_a_5653_);
    leanh::lean_dec(v_a_5652_);
    leanh::lean_dec_ref(v_a_5651_);
    return v_res_5657_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(
    mut v_pu_5658_: u8,
    mut v_inst_5659_: *mut leanh::LeanObject,
    mut v_R_5660_: *mut leanh::LeanObject,
    mut v_a_5661_: *mut leanh::LeanObject,
    mut v_b_5662_: *mut leanh::LeanObject,
    mut v_c_5663_: *mut leanh::LeanObject,
    mut v___y_5664_: *mut leanh::LeanObject,
    mut v___y_5665_: *mut leanh::LeanObject,
    mut v___y_5666_: *mut leanh::LeanObject,
    mut v___y_5667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(v_pu_5658_, v_a_5661_, v_b_5662_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_);
    return v___x_5669_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(
    mut v_pu_5670_: *mut leanh::LeanObject,
    mut v_inst_5671_: *mut leanh::LeanObject,
    mut v_R_5672_: *mut leanh::LeanObject,
    mut v_a_5673_: *mut leanh::LeanObject,
    mut v_b_5674_: *mut leanh::LeanObject,
    mut v_c_5675_: *mut leanh::LeanObject,
    mut v___y_5676_: *mut leanh::LeanObject,
    mut v___y_5677_: *mut leanh::LeanObject,
    mut v___y_5678_: *mut leanh::LeanObject,
    mut v___y_5679_: *mut leanh::LeanObject,
    mut v___y_5680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_5681_: u8 = 0;
    let mut v_res_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5681_ = (leanh::lean_unbox(v_pu_5670_) as u8);
    v_res_5682_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkCasesResultType_spec__0(
            v_pu_boxed_5681_,
            v_inst_5671_,
            v_R_5672_,
            v_a_5673_,
            v_b_5674_,
            v_c_5675_,
            v___y_5676_,
            v___y_5677_,
            v___y_5678_,
            v___y_5679_,
        );
    leanh::lean_dec(v___y_5679_);
    leanh::lean_dec_ref(v___y_5678_);
    leanh::lean_dec(v___y_5677_);
    leanh::lean_dec_ref(v___y_5676_);
    return v_res_5682_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(
    mut v_msg_5683_: *mut leanh::LeanObject,
    mut v___y_5684_: *mut leanh::LeanObject,
    mut v___y_5685_: *mut leanh::LeanObject,
    mut v___y_5686_: *mut leanh::LeanObject,
    mut v___y_5687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: u8 = 0;
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969__overap_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5689_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__1,
    );
    v_toApplicative_5690_ = leanh::lean_ctor_get(v___x_5689_, 0);
    v_toFunctor_5691_ = leanh::lean_ctor_get(v_toApplicative_5690_, 0);
    v_toSeq_5692_ = leanh::lean_ctor_get(v_toApplicative_5690_, 2);
    v_toSeqLeft_5693_ = leanh::lean_ctor_get(v_toApplicative_5690_, 3);
    v_toSeqRight_5694_ = leanh::lean_ctor_get(v_toApplicative_5690_, 4);
    v___f_5695_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__2;
    v___f_5696_ = l_Lean_Compiler_LCNF_InferType_Pure_withLocalDecl___redArg___closed__3;
    leanh::lean_inc_ref_n(v_toFunctor_5691_, 2);
    v___f_5697_ = leanh::lean_alloc_closure(
        l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5697_, 0, v_toFunctor_5691_);
    v___f_5698_ = leanh::lean_alloc_closure(
        l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5698_, 0, v_toFunctor_5691_);
    v___x_5699_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5699_, 0, v___f_5697_);
    leanh::lean_ctor_set(v___x_5699_, 1, v___f_5698_);
    leanh::lean_inc(v_toSeqRight_5694_);
    v___f_5700_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5700_, 0, v_toSeqRight_5694_);
    leanh::lean_inc(v_toSeqLeft_5693_);
    v___f_5701_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5701_, 0, v_toSeqLeft_5693_);
    leanh::lean_inc(v_toSeq_5692_);
    v___f_5702_ = leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_5702_, 0, v_toSeq_5692_);
    v___x_5703_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_5703_, 0, v___x_5699_);
    leanh::lean_ctor_set(v___x_5703_, 1, v___f_5695_);
    leanh::lean_ctor_set(v___x_5703_, 2, v___f_5702_);
    leanh::lean_ctor_set(v___x_5703_, 3, v___f_5701_);
    leanh::lean_ctor_set(v___x_5703_, 4, v___f_5700_);
    v___x_5704_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5704_, 0, v___x_5703_);
    leanh::lean_ctor_set(v___x_5704_, 1, v___f_5696_);
    v___x_5705_ = l_StateRefT_x27_instMonad___redArg(v___x_5704_);
    v___x_5706_ = 0;
    v___x_5707_ = leanh::lean_box((v___x_5706_) as usize);
    v___x_5708_ = l_instInhabitedOfMonad___redArg(v___x_5705_, v___x_5707_);
    v___f_5709_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5709_, 0, v___x_5708_);
    v___x_969__overap_5710_ = lean_panic_fn_borrowed(v___f_5709_, v_msg_5683_);
    leanh::lean_dec_ref(v___f_5709_);
    leanh::lean_inc(v___y_5687_);
    leanh::lean_inc_ref(v___y_5686_);
    leanh::lean_inc(v___y_5685_);
    leanh::lean_inc_ref(v___y_5684_);
    v___x_5711_ = leanh::lean_apply_5(
        v___x_969__overap_5710_,
        v___y_5684_,
        v___y_5685_,
        v___y_5686_,
        v___y_5687_,
        leanh::lean_box(0),
    );
    return v___x_5711_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0___boxed(
    mut v_msg_5712_: *mut leanh::LeanObject,
    mut v___y_5713_: *mut leanh::LeanObject,
    mut v___y_5714_: *mut leanh::LeanObject,
    mut v___y_5715_: *mut leanh::LeanObject,
    mut v___y_5716_: *mut leanh::LeanObject,
    mut v___y_5717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5718_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v_msg_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_);
    leanh::lean_dec(v___y_5716_);
    leanh::lean_dec_ref(v___y_5715_);
    leanh::lean_dec(v___y_5714_);
    leanh::lean_dec_ref(v___y_5713_);
    return v_res_5718_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5720_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__2;
    v___x_5721_ = leanh::lean_unsigned_to_nat(50);
    v___x_5722_ = leanh::lean_unsigned_to_nat(345);
    v___x_5723_ = l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__0;
    v___x_5724_ = l_Lean_Compiler_LCNF_InferType_Pure_inferType___closed__0;
    v___x_5725_ = l_mkPanicMessageWithDecl(
        v___x_5724_,
        v___x_5723_,
        v___x_5722_,
        v___x_5721_,
        v___x_5720_,
    );
    return v___x_5725_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(
    mut v_type_5726_: *mut leanh::LeanObject,
    mut v_predVars_5727_: *mut leanh::LeanObject,
    mut v_a_5728_: *mut leanh::LeanObject,
    mut v_a_5729_: *mut leanh::LeanObject,
    mut v_a_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: u8 = 0;
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5760_: u8 = 0;
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5765_: u8 = 0;
    let mut v_a_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5769_: u8 = 0;
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5773_: u8 = 0;
    let mut v___x_5774_: u8 = 0;
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_5744_ = l_Lean_Expr_headBeta(v_type_5726_);
                match leanh::lean_obj_tag(v_type_5744_) {
                    0 => {
                        v_deBruijnIndex_5745_ = leanh::lean_ctor_get(v_type_5744_, 0);
                        leanh::lean_inc(v_deBruijnIndex_5745_);
                        leanh::lean_dec_ref_known(v_type_5744_, 1);
                        v___x_5746_ = 0;
                        v___x_5747_ = lean_array_get_size(v_predVars_5727_);
                        v___x_5748_ = lean_nat_sub(v___x_5747_, v_deBruijnIndex_5745_);
                        leanh::lean_dec(v_deBruijnIndex_5745_);
                        v___x_5749_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5750_ = lean_nat_sub(v___x_5748_, v___x_5749_);
                        leanh::lean_dec(v___x_5748_);
                        v___x_5751_ = leanh::lean_box((v___x_5746_) as usize);
                        v___x_5752_ = lean_array_get(v___x_5751_, v_predVars_5727_, v___x_5750_);
                        leanh::lean_dec(v___x_5750_);
                        leanh::lean_dec_ref(v_predVars_5727_);
                        leanh::lean_dec(v___x_5751_);
                        v___x_5753_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5753_, 0, v___x_5752_);
                        return v___x_5753_;
                    }
                    1 => {
                        leanh::lean_dec_ref(v_predVars_5727_);
                        v_fvarId_5754_ = leanh::lean_ctor_get(v_type_5744_, 0);
                        leanh::lean_inc(v_fvarId_5754_);
                        leanh::lean_dec_ref_known(v_type_5744_, 1);
                        v___x_5755_ = l_Lean_Compiler_LCNF_getType(
                            v_fvarId_5754_,
                            v_a_5728_,
                            v_a_5729_,
                            v_a_5730_,
                            v_a_5731_,
                        );
                        if leanh::lean_obj_tag(v___x_5755_) == 0 {
                            v_a_5756_ = leanh::lean_ctor_get(v___x_5755_, 0);
                            v_isSharedCheck_5765_ =
                                (!leanh::lean_is_exclusive(v___x_5755_)) as u8;
                            if v_isSharedCheck_5765_ == 0 {
                                v___x_5758_ = v___x_5755_;
                                v_isShared_5759_ = v_isSharedCheck_5765_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5756_);
                                leanh::lean_dec(v___x_5755_);
                                v___x_5758_ = leanh::lean_box(0);
                                v_isShared_5759_ = v_isSharedCheck_5765_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_5766_ = leanh::lean_ctor_get(v___x_5755_, 0);
                            v_isSharedCheck_5773_ =
                                (!leanh::lean_is_exclusive(v___x_5755_)) as u8;
                            if v_isSharedCheck_5773_ == 0 {
                                v___x_5768_ = v___x_5755_;
                                v_isShared_5769_ = v_isSharedCheck_5773_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5766_);
                                leanh::lean_dec(v___x_5755_);
                                v___x_5768_ = leanh::lean_box(0);
                                v_isShared_5769_ = v_isSharedCheck_5773_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                    3 => {
                        leanh::lean_dec_ref_known(v_type_5744_, 1);
                        leanh::lean_dec_ref(v_predVars_5727_);
                        v___x_5774_ = 0;
                        v___x_5775_ = leanh::lean_box((v___x_5774_) as usize);
                        v___x_5776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5776_, 0, v___x_5775_);
                        return v___x_5776_;
                    }
                    4 => {
                        leanh::lean_dec_ref(v_predVars_5727_);
                        v___x_5777_ = l_Lean_Expr_isErased(v_type_5744_);
                        leanh::lean_dec_ref_known(v_type_5744_, 2);
                        v___x_5778_ = leanh::lean_box((v___x_5777_) as usize);
                        v___x_5779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
                        return v___x_5779_;
                    }
                    5 => {
                        v_fn_5780_ = leanh::lean_ctor_get(v_type_5744_, 0);
                        leanh::lean_inc_ref(v_fn_5780_);
                        leanh::lean_dec_ref_known(v_type_5744_, 2);
                        v_type_5726_ = v_fn_5780_;
                        state = 0;
                        continue;
                    }
                    6 => {
                        v_binderType_5782_ = leanh::lean_ctor_get(v_type_5744_, 1);
                        leanh::lean_inc_ref(v_binderType_5782_);
                        v_body_5783_ = leanh::lean_ctor_get(v_type_5744_, 2);
                        leanh::lean_inc_ref(v_body_5783_);
                        leanh::lean_dec_ref_known(v_type_5744_, 3);
                        v_t_5734_ = v_binderType_5782_;
                        v_b_5735_ = v_body_5783_;
                        v___y_5736_ = v_a_5728_;
                        v___y_5737_ = v_a_5729_;
                        v___y_5738_ = v_a_5730_;
                        v___y_5739_ = v_a_5731_;
                        state = 1;
                        continue;
                    }
                    7 => {
                        v_binderType_5784_ = leanh::lean_ctor_get(v_type_5744_, 1);
                        leanh::lean_inc_ref(v_binderType_5784_);
                        v_body_5785_ = leanh::lean_ctor_get(v_type_5744_, 2);
                        leanh::lean_inc_ref(v_body_5785_);
                        leanh::lean_dec_ref_known(v_type_5744_, 3);
                        v_t_5734_ = v_binderType_5784_;
                        v_b_5735_ = v_body_5785_;
                        v___y_5736_ = v_a_5728_;
                        v___y_5737_ = v_a_5729_;
                        v___y_5738_ = v_a_5730_;
                        v___y_5739_ = v_a_5731_;
                        state = 1;
                        continue;
                    }
                    10 => {
                        v_expr_5786_ = leanh::lean_ctor_get(v_type_5744_, 1);
                        leanh::lean_inc_ref(v_expr_5786_);
                        leanh::lean_dec_ref_known(v_type_5744_, 2);
                        v_type_5726_ = v_expr_5786_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref(v_type_5744_);
                        leanh::lean_dec_ref(v_predVars_5727_);
                        v___x_5788_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1_once), _init_l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
                        v___x_5789_ = l_panic___at___00__private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(v___x_5788_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_);
                        return v___x_5789_;
                    }
                }
            }
            1 => {
                v___x_5740_ = l_Lean_Compiler_LCNF_isPredicateType(v_t_5734_);
                v___x_5741_ = leanh::lean_box((v___x_5740_) as usize);
                v___x_5742_ = lean_array_push(v_predVars_5727_, v___x_5741_);
                v_type_5726_ = v_b_5735_;
                v_predVars_5727_ = v___x_5742_;
                v_a_5728_ = v___y_5736_;
                v_a_5729_ = v___y_5737_;
                v_a_5730_ = v___y_5738_;
                v_a_5731_ = v___y_5739_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5760_ = l_Lean_Compiler_LCNF_isPredicateType(v_a_5756_);
                v___x_5761_ = leanh::lean_box((v___x_5760_) as usize);
                if v_isShared_5759_ == 0 {
                    leanh::lean_ctor_set(v___x_5758_, 0, v___x_5761_);
                    v___x_5763_ = v___x_5758_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5764_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5761_);
                    v___x_5763_ = v_reuseFailAlloc_5764_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5763_;
            }
            4 => {
                if v_isShared_5769_ == 0 {
                    v___x_5771_ = v___x_5768_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_a_5766_);
                    v___x_5771_ = v_reuseFailAlloc_5772_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go___boxed(
    mut v_type_5790_: *mut leanh::LeanObject,
    mut v_predVars_5791_: *mut leanh::LeanObject,
    mut v_a_5792_: *mut leanh::LeanObject,
    mut v_a_5793_: *mut leanh::LeanObject,
    mut v_a_5794_: *mut leanh::LeanObject,
    mut v_a_5795_: *mut leanh::LeanObject,
    mut v_a_5796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5797_ =
        l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(
            v_type_5790_,
            v_predVars_5791_,
            v_a_5792_,
            v_a_5793_,
            v_a_5794_,
            v_a_5795_,
        );
    leanh::lean_dec(v_a_5795_);
    leanh::lean_dec_ref(v_a_5794_);
    leanh::lean_dec(v_a_5793_);
    leanh::lean_dec_ref(v_a_5792_);
    return v_res_5797_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isErasedCompatible(
    mut v_type_5798_: *mut leanh::LeanObject,
    mut v_predVars_5799_: *mut leanh::LeanObject,
    mut v_a_5800_: *mut leanh::LeanObject,
    mut v_a_5801_: *mut leanh::LeanObject,
    mut v_a_5802_: *mut leanh::LeanObject,
    mut v_a_5803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5805_ =
        l___private_Lean_Compiler_LCNF_InferType_0__Lean_Compiler_LCNF_isErasedCompatible_go(
            v_type_5798_,
            v_predVars_5799_,
            v_a_5800_,
            v_a_5801_,
            v_a_5802_,
            v_a_5803_,
        );
    return v___x_5805_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isErasedCompatible___boxed(
    mut v_type_5806_: *mut leanh::LeanObject,
    mut v_predVars_5807_: *mut leanh::LeanObject,
    mut v_a_5808_: *mut leanh::LeanObject,
    mut v_a_5809_: *mut leanh::LeanObject,
    mut v_a_5810_: *mut leanh::LeanObject,
    mut v_a_5811_: *mut leanh::LeanObject,
    mut v_a_5812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5813_ = l_Lean_Compiler_LCNF_isErasedCompatible(
        v_type_5806_,
        v_predVars_5807_,
        v_a_5808_,
        v_a_5809_,
        v_a_5810_,
        v_a_5811_,
    );
    leanh::lean_dec(v_a_5811_);
    leanh::lean_dec_ref(v_a_5810_);
    leanh::lean_dec(v_a_5809_);
    leanh::lean_dec_ref(v_a_5808_);
    return v_res_5813_;
}
pub unsafe fn l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(
    mut v_x_5814_: *mut leanh::LeanObject,
    mut v_x_5815_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5816_: u8 = 0;
    let mut v___x_5817_: u8 = 0;
    let mut v___x_5818_: u8 = 0;
    let mut v_head_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5814_) == 0 {
                    if leanh::lean_obj_tag(v_x_5815_) == 0 {
                        v___x_5816_ = 1;
                        return v___x_5816_;
                    } else {
                        v___x_5817_ = 0;
                        return v___x_5817_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_5815_) == 0 {
                        v___x_5818_ = 0;
                        return v___x_5818_;
                    } else {
                        v_head_5819_ = leanh::lean_ctor_get(v_x_5814_, 0);
                        v_tail_5820_ = leanh::lean_ctor_get(v_x_5814_, 1);
                        v_head_5821_ = leanh::lean_ctor_get(v_x_5815_, 0);
                        v_tail_5822_ = leanh::lean_ctor_get(v_x_5815_, 1);
                        v___x_5823_ = l_Lean_Level_isEquiv(v_head_5819_, v_head_5821_);
                        if v___x_5823_ == 0 {
                            return v___x_5823_;
                        } else {
                            v_x_5814_ = v_tail_5820_;
                            v_x_5815_ = v_tail_5822_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(
    mut v_x_5825_: *mut leanh::LeanObject,
    mut v_x_5826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5827_: u8 = 0;
    let mut v_r_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5827_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_x_5825_, v_x_5826_);
    leanh::lean_dec(v_x_5826_);
    leanh::lean_dec(v_x_5825_);
    v_r_5828_ = leanh::lean_box((v_res_5827_) as usize);
    return v_r_5828_;
}
pub unsafe fn l_Lean_Compiler_LCNF_eqvTypes(
    mut v_a_5829_: *mut leanh::LeanObject,
    mut v_b_5830_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_d_u2081_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_u2081_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_u2082_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_u2082_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: u8 = 0;
    let mut v___x_5838_: u8 = 0;
    let mut v___x_5839_: u8 = 0;
    let mut v___y_5841_: u8 = 0;
    let mut v_a_x27_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_x27_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: u8 = 0;
    let mut v___x_5846_: u8 = 0;
    let mut v_expr_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: u8 = 0;
    let mut v_expr_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: u8 = 0;
    let mut v_expr_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: u8 = 0;
    let mut v___x_5882_: u8 = 0;
    let mut v_expr_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: u8 = 0;
    let mut v___x_5886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5838_ = lean_expr_eqv(v_a_5829_, v_b_5830_);
                v___x_5839_ = 1;
                if v___x_5838_ == 0 {
                    v___x_5885_ = l_Lean_Expr_isErased(v_a_5829_);
                    if v___x_5885_ == 0 {
                        v___y_5841_ = v___x_5885_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5886_ = l_Lean_Expr_isErased(v_b_5830_);
                        v___y_5841_ = v___x_5886_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_5830_);
                    leanh::lean_dec_ref(v_a_5829_);
                    return v___x_5839_;
                }
            }
            1 => {
                v___x_5836_ = l_Lean_Compiler_LCNF_eqvTypes(v_d_u2081_5832_, v_d_u2082_5834_);
                if v___x_5836_ == 0 {
                    leanh::lean_dec_ref(v_b_u2082_5835_);
                    leanh::lean_dec_ref(v_b_u2081_5833_);
                    return v___x_5836_;
                } else {
                    v_a_5829_ = v_b_u2081_5833_;
                    v_b_5830_ = v_b_u2082_5835_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_5841_ == 0 {
                    leanh::lean_inc_ref(v_a_5829_);
                    v_a_x27_5842_ = l_Lean_Expr_headBeta(v_a_5829_);
                    leanh::lean_inc_ref(v_b_5830_);
                    v_b_x27_5843_ = l_Lean_Expr_headBeta(v_b_5830_);
                    v___x_5844_ = lean_expr_eqv(v_a_5829_, v_a_x27_5842_);
                    if v___x_5844_ == 0 {
                        leanh::lean_dec_ref(v_b_5830_);
                        leanh::lean_dec_ref(v_a_5829_);
                        v_a_5829_ = v_a_x27_5842_;
                        v_b_5830_ = v_b_x27_5843_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5846_ = lean_expr_eqv(v_b_5830_, v_b_x27_5843_);
                        if v___x_5846_ == 0 {
                            leanh::lean_dec_ref(v_b_5830_);
                            leanh::lean_dec_ref(v_a_5829_);
                            v_a_5829_ = v_a_x27_5842_;
                            v_b_5830_ = v_b_x27_5843_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_x27_5843_);
                            leanh::lean_dec_ref(v_a_x27_5842_);
                            match leanh::lean_obj_tag(v_a_5829_) {
                                10 => {
                                    v_expr_5848_ = leanh::lean_ctor_get(v_a_5829_, 1);
                                    leanh::lean_inc_ref(v_expr_5848_);
                                    leanh::lean_dec_ref_known(v_a_5829_, 2);
                                    v_a_5829_ = v_expr_5848_;
                                    state = 0;
                                    continue;
                                }
                                5 => match leanh::lean_obj_tag(v_b_5830_) {
                                    10 => {
                                        v_expr_5850_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_expr_5850_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v_b_5830_ = v_expr_5850_;
                                        state = 0;
                                        continue;
                                    }
                                    5 => {
                                        v_fn_5852_ = leanh::lean_ctor_get(v_a_5829_, 0);
                                        leanh::lean_inc_ref(v_fn_5852_);
                                        v_arg_5853_ = leanh::lean_ctor_get(v_a_5829_, 1);
                                        leanh::lean_inc_ref(v_arg_5853_);
                                        leanh::lean_dec_ref_known(v_a_5829_, 2);
                                        v_fn_5854_ = leanh::lean_ctor_get(v_b_5830_, 0);
                                        leanh::lean_inc_ref(v_fn_5854_);
                                        v_arg_5855_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_arg_5855_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v___x_5856_ =
                                            l_Lean_Compiler_LCNF_eqvTypes(v_fn_5852_, v_fn_5854_);
                                        if v___x_5856_ == 0 {
                                            leanh::lean_dec_ref(v_arg_5855_);
                                            leanh::lean_dec_ref(v_arg_5853_);
                                            return v___x_5856_;
                                        } else {
                                            v_a_5829_ = v_arg_5853_;
                                            v_b_5830_ = v_arg_5855_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                    _ => {
                                        leanh::lean_dec_ref_known(v_a_5829_, 2);
                                        leanh::lean_dec_ref(v_b_5830_);
                                        return v___y_5841_;
                                    }
                                },
                                7 => match leanh::lean_obj_tag(v_b_5830_) {
                                    10 => {
                                        v_expr_5858_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_expr_5858_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v_b_5830_ = v_expr_5858_;
                                        state = 0;
                                        continue;
                                    }
                                    7 => {
                                        v_binderType_5860_ =
                                            leanh::lean_ctor_get(v_a_5829_, 1);
                                        leanh::lean_inc_ref(v_binderType_5860_);
                                        v_body_5861_ = leanh::lean_ctor_get(v_a_5829_, 2);
                                        leanh::lean_inc_ref(v_body_5861_);
                                        leanh::lean_dec_ref_known(v_a_5829_, 3);
                                        v_binderType_5862_ =
                                            leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_binderType_5862_);
                                        v_body_5863_ = leanh::lean_ctor_get(v_b_5830_, 2);
                                        leanh::lean_inc_ref(v_body_5863_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 3);
                                        v_d_u2081_5832_ = v_binderType_5860_;
                                        v_b_u2081_5833_ = v_body_5861_;
                                        v_d_u2082_5834_ = v_binderType_5862_;
                                        v_b_u2082_5835_ = v_body_5863_;
                                        state = 1;
                                        continue;
                                    }
                                    _ => {
                                        leanh::lean_dec_ref_known(v_a_5829_, 3);
                                        leanh::lean_dec_ref(v_b_5830_);
                                        return v___y_5841_;
                                    }
                                },
                                6 => match leanh::lean_obj_tag(v_b_5830_) {
                                    10 => {
                                        v_expr_5864_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_expr_5864_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v_b_5830_ = v_expr_5864_;
                                        state = 0;
                                        continue;
                                    }
                                    6 => {
                                        v_binderType_5866_ =
                                            leanh::lean_ctor_get(v_a_5829_, 1);
                                        leanh::lean_inc_ref(v_binderType_5866_);
                                        v_body_5867_ = leanh::lean_ctor_get(v_a_5829_, 2);
                                        leanh::lean_inc_ref(v_body_5867_);
                                        leanh::lean_dec_ref_known(v_a_5829_, 3);
                                        v_binderType_5868_ =
                                            leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_binderType_5868_);
                                        v_body_5869_ = leanh::lean_ctor_get(v_b_5830_, 2);
                                        leanh::lean_inc_ref(v_body_5869_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 3);
                                        v_d_u2081_5832_ = v_binderType_5866_;
                                        v_b_u2081_5833_ = v_body_5867_;
                                        v_d_u2082_5834_ = v_binderType_5868_;
                                        v_b_u2082_5835_ = v_body_5869_;
                                        state = 1;
                                        continue;
                                    }
                                    _ => {
                                        leanh::lean_dec_ref_known(v_a_5829_, 3);
                                        leanh::lean_dec_ref(v_b_5830_);
                                        return v___y_5841_;
                                    }
                                },
                                3 => match leanh::lean_obj_tag(v_b_5830_) {
                                    10 => {
                                        v_expr_5870_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_expr_5870_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v_b_5830_ = v_expr_5870_;
                                        state = 0;
                                        continue;
                                    }
                                    3 => {
                                        v_u_5872_ = leanh::lean_ctor_get(v_a_5829_, 0);
                                        leanh::lean_inc(v_u_5872_);
                                        leanh::lean_dec_ref_known(v_a_5829_, 1);
                                        v_u_5873_ = leanh::lean_ctor_get(v_b_5830_, 0);
                                        leanh::lean_inc(v_u_5873_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 1);
                                        v___x_5874_ = l_Lean_Level_isEquiv(v_u_5872_, v_u_5873_);
                                        leanh::lean_dec(v_u_5873_);
                                        leanh::lean_dec(v_u_5872_);
                                        return v___x_5874_;
                                    }
                                    _ => {
                                        leanh::lean_dec_ref_known(v_a_5829_, 1);
                                        leanh::lean_dec_ref(v_b_5830_);
                                        return v___y_5841_;
                                    }
                                },
                                4 => match leanh::lean_obj_tag(v_b_5830_) {
                                    10 => {
                                        v_expr_5875_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_expr_5875_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v_b_5830_ = v_expr_5875_;
                                        state = 0;
                                        continue;
                                    }
                                    4 => {
                                        v_declName_5877_ =
                                            leanh::lean_ctor_get(v_a_5829_, 0);
                                        leanh::lean_inc(v_declName_5877_);
                                        v_us_5878_ = leanh::lean_ctor_get(v_a_5829_, 1);
                                        leanh::lean_inc(v_us_5878_);
                                        leanh::lean_dec_ref_known(v_a_5829_, 2);
                                        v_declName_5879_ =
                                            leanh::lean_ctor_get(v_b_5830_, 0);
                                        leanh::lean_inc(v_declName_5879_);
                                        v_us_5880_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc(v_us_5880_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v___x_5881_ =
                                            lean_name_eq(v_declName_5877_, v_declName_5879_);
                                        leanh::lean_dec(v_declName_5879_);
                                        leanh::lean_dec(v_declName_5877_);
                                        if v___x_5881_ == 0 {
                                            leanh::lean_dec(v_us_5880_);
                                            leanh::lean_dec(v_us_5878_);
                                            return v___x_5881_;
                                        } else {
                                            v___x_5882_ = l_List_isEqv___at___00Lean_Compiler_LCNF_eqvTypes_spec__0(v_us_5878_, v_us_5880_);
                                            leanh::lean_dec(v_us_5880_);
                                            leanh::lean_dec(v_us_5878_);
                                            return v___x_5882_;
                                        }
                                    }
                                    _ => {
                                        leanh::lean_dec_ref_known(v_a_5829_, 2);
                                        leanh::lean_dec_ref(v_b_5830_);
                                        return v___y_5841_;
                                    }
                                },
                                _ => {
                                    if leanh::lean_obj_tag(v_b_5830_) == 10 {
                                        v_expr_5883_ = leanh::lean_ctor_get(v_b_5830_, 1);
                                        leanh::lean_inc_ref(v_expr_5883_);
                                        leanh::lean_dec_ref_known(v_b_5830_, 2);
                                        v_b_5830_ = v_expr_5883_;
                                        state = 0;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_b_5830_);
                                        leanh::lean_dec_ref(v_a_5829_);
                                        return v___y_5841_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_5830_);
                    leanh::lean_dec_ref(v_a_5829_);
                    return v___x_5839_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_eqvTypes___boxed(
    mut v_a_5887_: *mut leanh::LeanObject,
    mut v_b_5888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5889_: u8 = 0;
    let mut v_r_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5889_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_5887_, v_b_5888_);
    v_r_5890_ = leanh::lean_box((v_res_5889_) as usize);
    return v_r_5890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_InferType(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
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
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_InferType(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_InferType(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_OtherDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_InferType(builtin);
}