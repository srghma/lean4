// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineCandidate
// Imports: Lean.Compiler.LCNF.Simp.SimpM
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams,
    l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg,
    l_Lean_Compiler_LCNF_Decl_getArity___redArg, l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg,
    l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg,
    l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams,
    l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg,
    l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg,
    l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg, l_Lean_Compiler_LCNF_Phase_toPurity,
    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg, l_Lean_Compiler_LCNF_findParam_x3f___redArg,
    l_Lean_Compiler_LCNF_getPhase___redArg, l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_getType, l_Lean_Compiler_LCNF_inBasePhase___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    l_Lean_Compiler_LCNF_getDeclAt_x3f, l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Basic::l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    initialize_Lean_Compiler_LCNF_Simp_SimpM, l_Lean_Compiler_LCNF_Simp_incInline___redArg,
    l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg,
    l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed,
    l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed,
    l_Lean_Compiler_LCNF_Simp_isSmall___redArg,
    l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Instances::l_Lean_Meta_isInstance___redArg;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [95, 111, 118, 101, 114, 114, 105, 100, 101, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value:
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
        105, 110, 115, 116, 68, 101, 99, 105, 100, 97, 98, 108, 101, 69, 113, 66, 111, 111, 108, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6289368979427661087 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 108, 105, 110, 101, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value:
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
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        96, 105, 110, 108, 105, 110, 101, 96, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111,
        32, 110, 111, 110, 45, 108, 111, 99, 97, 108, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105,
        111, 110, 32, 39, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value:
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
    m_data: [39, 32, 105, 115, 32, 105, 110, 118, 97, 108, 105, 100, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value:
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
        96, 105, 110, 108, 105, 110, 101, 96, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111,
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 39, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        105, 109, 112, 46, 73, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101,
        0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83,
        105, 109, 112, 46, 105, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101,
        63, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value:
    crate::leanh::LeanStringObject<121> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 121,
    m_capacity: 121,
    m_length: 120,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110,
        46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46,
        73, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101, 46, 52, 53, 48, 49,
        53, 48, 50, 49, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 51, 51,
        54, 46, 48, 32, 41, 46, 105, 115, 83, 111, 109, 101, 10, 32, 32, 32, 32, 32, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        96, 105, 110, 108, 105, 110, 101, 96, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111,
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 115, 32, 105, 110, 118, 97,
        108, 105, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11260351269579028997 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value) as *mut crate::leanh::LeanObject,7114391375504651962 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12083366481402619969 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [73, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3196211847899758028 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9036830464040704205 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16082240727276424632 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18273738737171653778 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1953136760100813779 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11981961001735387515 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7736829225013705930 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6854742905612141859 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1164919087555456622 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5416371453231879756 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11551569653759660685 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,322563206818071653 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13807283630111217176 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1449551352 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,936188780658061096 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15369283736512935311 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15053872815982515831 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14718621728666061922 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(
    mut v_x_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_params_1046_ = crate::leanh::lean_ctor_get(v_x_1045_, 0);
    v___x_1047_ = lean_array_get_size(v_params_1046_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(
    mut v_x_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_x_1048_);
    crate::leanh::lean_dec_ref(v_x_1048_);
    return v_res_1049_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0);
    v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1);
    v___x_1054_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1055_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1055_, 0, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 1, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 2, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 3, v___x_1054_);
    crate::leanh::lean_ctor_set(v___x_1055_, 4, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 5, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 6, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 7, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 8, v___x_1053_);
    crate::leanh::lean_ctor_set(v___x_1055_, 9, v___x_1053_);
    return v___x_1055_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(
    mut v_msg_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
    mut v___y_1058_: *mut crate::leanh::LeanObject,
    mut v___y_1059_: *mut crate::leanh::LeanObject,
    mut v___y_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v_env_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v___x_1076_: u8 = 0;
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_unused_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v_a_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1062_ = crate::leanh::lean_ctor_get(v___y_1059_, 2);
                v_ref_1063_ = crate::leanh::lean_ctor_get(v___y_1059_, 5);
                v___x_1064_ = lean_st_ref_get(v___y_1060_);
                v___x_1065_ = lean_st_ref_get(v___y_1058_);
                v___x_1066_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1057_);
                if crate::leanh::lean_obj_tag(v___x_1066_) == 0 {
                    v_a_1067_ = crate::leanh::lean_ctor_get(v___x_1066_, 0);
                    v_isSharedCheck_1089_ = (!crate::leanh::lean_is_exclusive(v___x_1066_)) as u8;
                    if v_isSharedCheck_1089_ == 0 {
                        v___x_1069_ = v___x_1066_;
                        v_isShared_1070_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1067_);
                        crate::leanh::lean_dec(v___x_1066_);
                        v___x_1069_ = crate::leanh::lean_box(0);
                        v_isShared_1070_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1065_);
                    crate::leanh::lean_dec(v___x_1064_);
                    crate::leanh::lean_dec_ref(v_msg_1056_);
                    v_a_1090_ = crate::leanh::lean_ctor_get(v___x_1066_, 0);
                    v_isSharedCheck_1097_ = (!crate::leanh::lean_is_exclusive(v___x_1066_)) as u8;
                    if v_isSharedCheck_1097_ == 0 {
                        v___x_1092_ = v___x_1066_;
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1090_);
                        crate::leanh::lean_dec(v___x_1066_);
                        v___x_1092_ = crate::leanh::lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_1071_ = crate::leanh::lean_ctor_get(v___x_1064_, 0);
                crate::leanh::lean_inc_ref(v_env_1071_);
                crate::leanh::lean_dec(v___x_1064_);
                v_lctx_1072_ = crate::leanh::lean_ctor_get(v___x_1065_, 0);
                v_isSharedCheck_1087_ = (!crate::leanh::lean_is_exclusive(v___x_1065_)) as u8;
                if v_isSharedCheck_1087_ == 0 {
                    v_unused_1088_ = crate::leanh::lean_ctor_get(v___x_1065_, 1);
                    crate::leanh::lean_dec(v_unused_1088_);
                    v___x_1074_ = v___x_1065_;
                    v_isShared_1075_ = v_isSharedCheck_1087_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_1072_);
                    crate::leanh::lean_dec(v___x_1065_);
                    v___x_1074_ = crate::leanh::lean_box(0);
                    v_isShared_1075_ = v_isSharedCheck_1087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1076_ = (crate::leanh::lean_unbox(v_a_1067_) as u8);
                crate::leanh::lean_dec(v_a_1067_);
                v___x_1077_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1072_, v___x_1076_);
                crate::leanh::lean_dec_ref(v_lctx_1072_);
                v___x_1078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2);
                crate::leanh::lean_inc_ref(v_options_1062_);
                v___x_1079_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1079_, 0, v_env_1071_);
                crate::leanh::lean_ctor_set(v___x_1079_, 1, v___x_1078_);
                crate::leanh::lean_ctor_set(v___x_1079_, 2, v___x_1077_);
                crate::leanh::lean_ctor_set(v___x_1079_, 3, v_options_1062_);
                if v_isShared_1075_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1074_, 3);
                    crate::leanh::lean_ctor_set(v___x_1074_, 1, v_msg_1056_);
                    crate::leanh::lean_ctor_set(v___x_1074_, 0, v___x_1079_);
                    v___x_1081_ = v___x_1074_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_msg_1056_);
                    v___x_1081_ = v_reuseFailAlloc_1086_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_1063_);
                v___x_1082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1082_, 0, v_ref_1063_);
                crate::leanh::lean_ctor_set(v___x_1082_, 1, v___x_1081_);
                if v_isShared_1070_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1069_, 1);
                    crate::leanh::lean_ctor_set(v___x_1069_, 0, v___x_1082_);
                    v___x_1084_ = v___x_1069_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
                    v___x_1084_ = v_reuseFailAlloc_1085_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1084_;
            }
            5 => {
                if v_isShared_1093_ == 0 {
                    v___x_1095_ = v___x_1092_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
                    v___x_1095_ = v_reuseFailAlloc_1096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___boxed(
    mut v_msg_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(
            v_msg_1098_,
            v___y_1099_,
            v___y_1100_,
            v___y_1101_,
            v___y_1102_,
        );
    crate::leanh::lean_dec(v___y_1102_);
    crate::leanh::lean_dec_ref(v___y_1101_);
    crate::leanh::lean_dec(v___y_1100_);
    crate::leanh::lean_dec_ref(v___y_1099_);
    return v_res_1104_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(
    mut v_00_u03b1_1105_: *mut crate::leanh::LeanObject,
    mut v_msg_1106_: *mut crate::leanh::LeanObject,
    mut v___y_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
    mut v___y_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(
            v_msg_1106_,
            v___y_1110_,
            v___y_1111_,
            v___y_1112_,
            v___y_1113_,
        );
    return v___x_1115_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___boxed(
    mut v_00_u03b1_1116_: *mut crate::leanh::LeanObject,
    mut v_msg_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(
        v_00_u03b1_1116_,
        v_msg_1117_,
        v___y_1118_,
        v___y_1119_,
        v___y_1120_,
        v___y_1121_,
        v___y_1122_,
        v___y_1123_,
        v___y_1124_,
    );
    crate::leanh::lean_dec(v___y_1124_);
    crate::leanh::lean_dec_ref(v___y_1123_);
    crate::leanh::lean_dec(v___y_1122_);
    crate::leanh::lean_dec_ref(v___y_1121_);
    crate::leanh::lean_dec_ref(v___y_1120_);
    crate::leanh::lean_dec(v___y_1119_);
    crate::leanh::lean_dec_ref(v___y_1118_);
    return v_res_1126_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1127_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(
    mut v_msg_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v_toFunctor_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___f_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v_toFunctor_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___f_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_21341__overap_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1199_: u8 = 0;
    let mut v_unused_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_unused_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_unused_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut v_unused_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1141_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
                v___x_1142_ = l_StateRefT_x27_instMonad___redArg(v___x_1141_);
                v_toApplicative_1143_ = crate::leanh::lean_ctor_get(v___x_1142_, 0);
                v_isSharedCheck_1207_ = (!crate::leanh::lean_is_exclusive(v___x_1142_)) as u8;
                if v_isSharedCheck_1207_ == 0 {
                    v_unused_1208_ = crate::leanh::lean_ctor_get(v___x_1142_, 1);
                    crate::leanh::lean_dec(v_unused_1208_);
                    v___x_1145_ = v___x_1142_;
                    v_isShared_1146_ = v_isSharedCheck_1207_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1143_);
                    crate::leanh::lean_dec(v___x_1142_);
                    v___x_1145_ = crate::leanh::lean_box(0);
                    v_isShared_1146_ = v_isSharedCheck_1207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1147_ = crate::leanh::lean_ctor_get(v_toApplicative_1143_, 0);
                v_toSeq_1148_ = crate::leanh::lean_ctor_get(v_toApplicative_1143_, 2);
                v_toSeqLeft_1149_ = crate::leanh::lean_ctor_get(v_toApplicative_1143_, 3);
                v_toSeqRight_1150_ = crate::leanh::lean_ctor_get(v_toApplicative_1143_, 4);
                v_isSharedCheck_1205_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1143_)) as u8;
                if v_isSharedCheck_1205_ == 0 {
                    v_unused_1206_ = crate::leanh::lean_ctor_get(v_toApplicative_1143_, 1);
                    crate::leanh::lean_dec(v_unused_1206_);
                    v___x_1152_ = v_toApplicative_1143_;
                    v_isShared_1153_ = v_isSharedCheck_1205_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1150_);
                    crate::leanh::lean_inc(v_toSeqLeft_1149_);
                    crate::leanh::lean_inc(v_toSeq_1148_);
                    crate::leanh::lean_inc(v_toFunctor_1147_);
                    crate::leanh::lean_dec(v_toApplicative_1143_);
                    v___x_1152_ = crate::leanh::lean_box(0);
                    v_isShared_1153_ = v_isSharedCheck_1205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1154_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1;
                v___f_1155_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1147_);
                v___f_1156_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1156_, 0, v_toFunctor_1147_);
                v___f_1157_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1157_, 0, v_toFunctor_1147_);
                v___x_1158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1158_, 0, v___f_1156_);
                crate::leanh::lean_ctor_set(v___x_1158_, 1, v___f_1157_);
                v___f_1159_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1159_, 0, v_toSeqRight_1150_);
                v___f_1160_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1160_, 0, v_toSeqLeft_1149_);
                v___f_1161_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1161_, 0, v_toSeq_1148_);
                if v_isShared_1153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1152_, 4, v___f_1159_);
                    crate::leanh::lean_ctor_set(v___x_1152_, 3, v___f_1160_);
                    crate::leanh::lean_ctor_set(v___x_1152_, 2, v___f_1161_);
                    crate::leanh::lean_ctor_set(v___x_1152_, 1, v___f_1154_);
                    crate::leanh::lean_ctor_set(v___x_1152_, 0, v___x_1158_);
                    v___x_1163_ = v___x_1152_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___f_1154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 2, v___f_1161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___f_1160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___f_1159_);
                    v___x_1163_ = v_reuseFailAlloc_1204_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1145_, 1, v___f_1155_);
                    crate::leanh::lean_ctor_set(v___x_1145_, 0, v___x_1163_);
                    v___x_1165_ = v___x_1145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___f_1155_);
                    v___x_1165_ = v_reuseFailAlloc_1203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1166_ = l_StateRefT_x27_instMonad___redArg(v___x_1165_);
                v_toApplicative_1167_ = crate::leanh::lean_ctor_get(v___x_1166_, 0);
                v_isSharedCheck_1201_ = (!crate::leanh::lean_is_exclusive(v___x_1166_)) as u8;
                if v_isSharedCheck_1201_ == 0 {
                    v_unused_1202_ = crate::leanh::lean_ctor_get(v___x_1166_, 1);
                    crate::leanh::lean_dec(v_unused_1202_);
                    v___x_1169_ = v___x_1166_;
                    v_isShared_1170_ = v_isSharedCheck_1201_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1167_);
                    crate::leanh::lean_dec(v___x_1166_);
                    v___x_1169_ = crate::leanh::lean_box(0);
                    v_isShared_1170_ = v_isSharedCheck_1201_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1171_ = crate::leanh::lean_ctor_get(v_toApplicative_1167_, 0);
                v_toSeq_1172_ = crate::leanh::lean_ctor_get(v_toApplicative_1167_, 2);
                v_toSeqLeft_1173_ = crate::leanh::lean_ctor_get(v_toApplicative_1167_, 3);
                v_toSeqRight_1174_ = crate::leanh::lean_ctor_get(v_toApplicative_1167_, 4);
                v_isSharedCheck_1199_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1167_)) as u8;
                if v_isSharedCheck_1199_ == 0 {
                    v_unused_1200_ = crate::leanh::lean_ctor_get(v_toApplicative_1167_, 1);
                    crate::leanh::lean_dec(v_unused_1200_);
                    v___x_1176_ = v_toApplicative_1167_;
                    v_isShared_1177_ = v_isSharedCheck_1199_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1174_);
                    crate::leanh::lean_inc(v_toSeqLeft_1173_);
                    crate::leanh::lean_inc(v_toSeq_1172_);
                    crate::leanh::lean_inc(v_toFunctor_1171_);
                    crate::leanh::lean_dec(v_toApplicative_1167_);
                    v___x_1176_ = crate::leanh::lean_box(0);
                    v_isShared_1177_ = v_isSharedCheck_1199_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1178_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3;
                v___f_1179_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1171_);
                v___f_1180_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1180_, 0, v_toFunctor_1171_);
                v___f_1181_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1181_, 0, v_toFunctor_1171_);
                v___x_1182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1182_, 0, v___f_1180_);
                crate::leanh::lean_ctor_set(v___x_1182_, 1, v___f_1181_);
                v___f_1183_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1183_, 0, v_toSeqRight_1174_);
                v___f_1184_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1184_, 0, v_toSeqLeft_1173_);
                v___f_1185_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1185_, 0, v_toSeq_1172_);
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1176_, 4, v___f_1183_);
                    crate::leanh::lean_ctor_set(v___x_1176_, 3, v___f_1184_);
                    crate::leanh::lean_ctor_set(v___x_1176_, 2, v___f_1185_);
                    crate::leanh::lean_ctor_set(v___x_1176_, 1, v___f_1178_);
                    crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1182_);
                    v___x_1187_ = v___x_1176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1198_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___f_1178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 2, v___f_1185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 3, v___f_1184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 4, v___f_1183_);
                    v___x_1187_ = v_reuseFailAlloc_1198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1169_, 1, v___f_1179_);
                    crate::leanh::lean_ctor_set(v___x_1169_, 0, v___x_1187_);
                    v___x_1189_ = v___x_1169_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___f_1179_);
                    v___x_1189_ = v_reuseFailAlloc_1197_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1190_ = l_ReaderT_instMonad___redArg(v___x_1189_);
                v___x_1191_ = l_StateRefT_x27_instMonad___redArg(v___x_1190_);
                v___x_1192_ = crate::leanh::lean_box(0);
                v___x_1193_ = l_instInhabitedOfMonad___redArg(v___x_1191_, v___x_1192_);
                v___f_1194_ = crate::leanh::lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1194_, 0, v___x_1193_);
                v___x_21341__overap_1195_ = lean_panic_fn_borrowed(v___f_1194_, v_msg_1132_);
                crate::leanh::lean_dec_ref(v___f_1194_);
                crate::leanh::lean_inc(v___y_1139_);
                crate::leanh::lean_inc_ref(v___y_1138_);
                crate::leanh::lean_inc(v___y_1137_);
                crate::leanh::lean_inc_ref(v___y_1136_);
                crate::leanh::lean_inc_ref(v___y_1135_);
                crate::leanh::lean_inc(v___y_1134_);
                crate::leanh::lean_inc_ref(v___y_1133_);
                v___x_1196_ = crate::leanh::lean_apply_8(
                    v___x_21341__overap_1195_,
                    v___y_1133_,
                    v___y_1134_,
                    v___y_1135_,
                    v___y_1136_,
                    v___y_1137_,
                    v___y_1138_,
                    v___y_1139_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(
    mut v_msg_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1218_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(
        v_msg_1209_,
        v___y_1210_,
        v___y_1211_,
        v___y_1212_,
        v___y_1213_,
        v___y_1214_,
        v___y_1215_,
        v___y_1216_,
    );
    crate::leanh::lean_dec(v___y_1216_);
    crate::leanh::lean_dec_ref(v___y_1215_);
    crate::leanh::lean_dec(v___y_1214_);
    crate::leanh::lean_dec_ref(v___y_1213_);
    crate::leanh::lean_dec_ref(v___y_1212_);
    crate::leanh::lean_dec(v___y_1211_);
    crate::leanh::lean_dec_ref(v___y_1210_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(
    mut v_val_1219_: *mut crate::leanh::LeanObject,
    mut v___x_1220_: u8,
    mut v_code_1221_: *mut crate::leanh::LeanObject,
    mut v_mustInline_1222_: u8,
    mut v_inlineDefs_1223_: u8,
    mut v_____r_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: u8 = 0;
    v___x_1233_ = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(v_val_1219_);
    if v___x_1233_ == 0 {
        let mut v___x_1234_: u8 = 0;
        v___x_1234_ = l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(v_val_1219_);
        if v___x_1234_ == 0 {
            if v___x_1220_ == 0 {
                let mut v___x_1235_: u8 = 0;
                v___x_1235_ = l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(v_val_1219_);
                if v___x_1235_ == 0 {
                    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1236_ =
                        l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1221_, v___y_1228_);
                    return v___x_1236_;
                } else {
                    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1237_ = crate::leanh::lean_box((v_mustInline_1222_) as usize);
                    v___x_1238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
                    return v___x_1238_;
                }
            } else {
                let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1239_ = crate::leanh::lean_box((v_inlineDefs_1223_) as usize);
                v___x_1240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1240_, 0, v___x_1239_);
                return v___x_1240_;
            }
        } else {
            let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1241_ = crate::leanh::lean_box((v_inlineDefs_1223_) as usize);
            v___x_1242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1242_, 0, v___x_1241_);
            return v___x_1242_;
        }
    } else {
        let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1243_ = crate::leanh::lean_box((v_inlineDefs_1223_) as usize);
        v___x_1244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1244_, 0, v___x_1243_);
        return v___x_1244_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(
    mut v_val_1245_: *mut crate::leanh::LeanObject,
    mut v___x_1246_: *mut crate::leanh::LeanObject,
    mut v_code_1247_: *mut crate::leanh::LeanObject,
    mut v_mustInline_1248_: *mut crate::leanh::LeanObject,
    mut v_inlineDefs_1249_: *mut crate::leanh::LeanObject,
    mut v_____r_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_21877__boxed_1259_: u8 = 0;
    let mut v_mustInline_boxed_1260_: u8 = 0;
    let mut v_inlineDefs_boxed_1261_: u8 = 0;
    let mut v_res_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21877__boxed_1259_ = (crate::leanh::lean_unbox(v___x_1246_) as u8);
    v_mustInline_boxed_1260_ = (crate::leanh::lean_unbox(v_mustInline_1248_) as u8);
    v_inlineDefs_boxed_1261_ = (crate::leanh::lean_unbox(v_inlineDefs_1249_) as u8);
    v_res_1262_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(
        v_val_1245_,
        v___x_21877__boxed_1259_,
        v_code_1247_,
        v_mustInline_boxed_1260_,
        v_inlineDefs_boxed_1261_,
        v_____r_1250_,
        v___y_1251_,
        v___y_1252_,
        v___y_1253_,
        v___y_1254_,
        v___y_1255_,
        v___y_1256_,
        v___y_1257_,
    );
    crate::leanh::lean_dec(v___y_1257_);
    crate::leanh::lean_dec_ref(v___y_1256_);
    crate::leanh::lean_dec(v___y_1255_);
    crate::leanh::lean_dec_ref(v___y_1254_);
    crate::leanh::lean_dec_ref(v___y_1253_);
    crate::leanh::lean_dec(v___y_1252_);
    crate::leanh::lean_dec_ref(v___y_1251_);
    crate::leanh::lean_dec_ref(v_code_1247_);
    crate::leanh::lean_dec_ref(v_val_1245_);
    return v_res_1262_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(
    mut v___f_1264_: *mut crate::leanh::LeanObject,
    mut v_name_1265_: *mut crate::leanh::LeanObject,
    mut v_mustInline_1266_: u8,
    mut v_____r_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_name_1265_) == 1 {
                    v_str_1279_ = crate::leanh::lean_ctor_get(v_name_1265_, 1);
                    v___x_1280_ =
                        l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0;
                    v___x_1281_ = lean_string_dec_eq(v_str_1279_, v___x_1280_);
                    if v___x_1281_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_1264_);
                        v___x_1282_ = crate::leanh::lean_box((v_mustInline_1266_) as usize);
                        v___x_1283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1283_, 0, v___x_1282_);
                        return v___x_1283_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1277_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_1274_);
                crate::leanh::lean_inc_ref(v___y_1273_);
                crate::leanh::lean_inc(v___y_1272_);
                crate::leanh::lean_inc_ref(v___y_1271_);
                crate::leanh::lean_inc_ref(v___y_1270_);
                crate::leanh::lean_inc(v___y_1269_);
                crate::leanh::lean_inc_ref(v___y_1268_);
                v___x_1278_ = crate::leanh::lean_apply_9(
                    v___f_1264_,
                    v___x_1277_,
                    v___y_1268_,
                    v___y_1269_,
                    v___y_1270_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___y_1274_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(
    mut v___f_1284_: *mut crate::leanh::LeanObject,
    mut v_name_1285_: *mut crate::leanh::LeanObject,
    mut v_mustInline_1286_: *mut crate::leanh::LeanObject,
    mut v_____r_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_1296_ = (crate::leanh::lean_unbox(v_mustInline_1286_) as u8);
    v_res_1297_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(
        v___f_1284_,
        v_name_1285_,
        v_mustInline_boxed_1296_,
        v_____r_1287_,
        v___y_1288_,
        v___y_1289_,
        v___y_1290_,
        v___y_1291_,
        v___y_1292_,
        v___y_1293_,
        v___y_1294_,
    );
    crate::leanh::lean_dec(v___y_1294_);
    crate::leanh::lean_dec_ref(v___y_1293_);
    crate::leanh::lean_dec(v___y_1292_);
    crate::leanh::lean_dec_ref(v___y_1291_);
    crate::leanh::lean_dec_ref(v___y_1290_);
    crate::leanh::lean_dec(v___y_1289_);
    crate::leanh::lean_dec_ref(v___y_1288_);
    crate::leanh::lean_dec(v_name_1285_);
    return v_res_1297_;
}
pub unsafe fn l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(
    mut v_msg_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v_toFunctor_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___f_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v_toFunctor_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___f_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v_toFunctor_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___f_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_21356__overap_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_unused_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1391_: u8 = 0;
    let mut v_unused_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_unused_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v_unused_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v_unused_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut v_unused_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
                v___x_1310_ = l_StateRefT_x27_instMonad___redArg(v___x_1309_);
                v_toApplicative_1311_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                v_isSharedCheck_1403_ = (!crate::leanh::lean_is_exclusive(v___x_1310_)) as u8;
                if v_isSharedCheck_1403_ == 0 {
                    v_unused_1404_ = crate::leanh::lean_ctor_get(v___x_1310_, 1);
                    crate::leanh::lean_dec(v_unused_1404_);
                    v___x_1313_ = v___x_1310_;
                    v_isShared_1314_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1311_);
                    crate::leanh::lean_dec(v___x_1310_);
                    v___x_1313_ = crate::leanh::lean_box(0);
                    v_isShared_1314_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1315_ = crate::leanh::lean_ctor_get(v_toApplicative_1311_, 0);
                v_toSeq_1316_ = crate::leanh::lean_ctor_get(v_toApplicative_1311_, 2);
                v_toSeqLeft_1317_ = crate::leanh::lean_ctor_get(v_toApplicative_1311_, 3);
                v_toSeqRight_1318_ = crate::leanh::lean_ctor_get(v_toApplicative_1311_, 4);
                v_isSharedCheck_1401_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1311_)) as u8;
                if v_isSharedCheck_1401_ == 0 {
                    v_unused_1402_ = crate::leanh::lean_ctor_get(v_toApplicative_1311_, 1);
                    crate::leanh::lean_dec(v_unused_1402_);
                    v___x_1320_ = v_toApplicative_1311_;
                    v_isShared_1321_ = v_isSharedCheck_1401_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1318_);
                    crate::leanh::lean_inc(v_toSeqLeft_1317_);
                    crate::leanh::lean_inc(v_toSeq_1316_);
                    crate::leanh::lean_inc(v_toFunctor_1315_);
                    crate::leanh::lean_dec(v_toApplicative_1311_);
                    v___x_1320_ = crate::leanh::lean_box(0);
                    v_isShared_1321_ = v_isSharedCheck_1401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1322_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1;
                v___f_1323_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1315_);
                v___f_1324_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1324_, 0, v_toFunctor_1315_);
                v___f_1325_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1325_, 0, v_toFunctor_1315_);
                v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1326_, 0, v___f_1324_);
                crate::leanh::lean_ctor_set(v___x_1326_, 1, v___f_1325_);
                v___f_1327_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1327_, 0, v_toSeqRight_1318_);
                v___f_1328_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1328_, 0, v_toSeqLeft_1317_);
                v___f_1329_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1329_, 0, v_toSeq_1316_);
                if v_isShared_1321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1320_, 4, v___f_1327_);
                    crate::leanh::lean_ctor_set(v___x_1320_, 3, v___f_1328_);
                    crate::leanh::lean_ctor_set(v___x_1320_, 2, v___f_1329_);
                    crate::leanh::lean_ctor_set(v___x_1320_, 1, v___f_1322_);
                    crate::leanh::lean_ctor_set(v___x_1320_, 0, v___x_1326_);
                    v___x_1331_ = v___x_1320_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___f_1322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 2, v___f_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 3, v___f_1328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1400_, 4, v___f_1327_);
                    v___x_1331_ = v_reuseFailAlloc_1400_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1313_, 1, v___f_1323_);
                    crate::leanh::lean_ctor_set(v___x_1313_, 0, v___x_1331_);
                    v___x_1333_ = v___x_1313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1399_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___f_1323_);
                    v___x_1333_ = v_reuseFailAlloc_1399_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1334_ = l_StateRefT_x27_instMonad___redArg(v___x_1333_);
                v_toApplicative_1335_ = crate::leanh::lean_ctor_get(v___x_1334_, 0);
                v_isSharedCheck_1397_ = (!crate::leanh::lean_is_exclusive(v___x_1334_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v_unused_1398_ = crate::leanh::lean_ctor_get(v___x_1334_, 1);
                    crate::leanh::lean_dec(v_unused_1398_);
                    v___x_1337_ = v___x_1334_;
                    v_isShared_1338_ = v_isSharedCheck_1397_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1335_);
                    crate::leanh::lean_dec(v___x_1334_);
                    v___x_1337_ = crate::leanh::lean_box(0);
                    v_isShared_1338_ = v_isSharedCheck_1397_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1339_ = crate::leanh::lean_ctor_get(v_toApplicative_1335_, 0);
                v_toSeq_1340_ = crate::leanh::lean_ctor_get(v_toApplicative_1335_, 2);
                v_toSeqLeft_1341_ = crate::leanh::lean_ctor_get(v_toApplicative_1335_, 3);
                v_toSeqRight_1342_ = crate::leanh::lean_ctor_get(v_toApplicative_1335_, 4);
                v_isSharedCheck_1395_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1335_)) as u8;
                if v_isSharedCheck_1395_ == 0 {
                    v_unused_1396_ = crate::leanh::lean_ctor_get(v_toApplicative_1335_, 1);
                    crate::leanh::lean_dec(v_unused_1396_);
                    v___x_1344_ = v_toApplicative_1335_;
                    v_isShared_1345_ = v_isSharedCheck_1395_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1342_);
                    crate::leanh::lean_inc(v_toSeqLeft_1341_);
                    crate::leanh::lean_inc(v_toSeq_1340_);
                    crate::leanh::lean_inc(v_toFunctor_1339_);
                    crate::leanh::lean_dec(v_toApplicative_1335_);
                    v___x_1344_ = crate::leanh::lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1395_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1346_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3;
                v___f_1347_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1339_);
                v___f_1348_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1348_, 0, v_toFunctor_1339_);
                v___f_1349_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1349_, 0, v_toFunctor_1339_);
                v___x_1350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1350_, 0, v___f_1348_);
                crate::leanh::lean_ctor_set(v___x_1350_, 1, v___f_1349_);
                v___f_1351_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1351_, 0, v_toSeqRight_1342_);
                v___f_1352_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1352_, 0, v_toSeqLeft_1341_);
                v___f_1353_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1353_, 0, v_toSeq_1340_);
                if v_isShared_1345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1344_, 4, v___f_1351_);
                    crate::leanh::lean_ctor_set(v___x_1344_, 3, v___f_1352_);
                    crate::leanh::lean_ctor_set(v___x_1344_, 2, v___f_1353_);
                    crate::leanh::lean_ctor_set(v___x_1344_, 1, v___f_1346_);
                    crate::leanh::lean_ctor_set(v___x_1344_, 0, v___x_1350_);
                    v___x_1355_ = v___x_1344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___f_1346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 2, v___f_1353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___f_1352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 4, v___f_1351_);
                    v___x_1355_ = v_reuseFailAlloc_1394_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1337_, 1, v___f_1347_);
                    crate::leanh::lean_ctor_set(v___x_1337_, 0, v___x_1355_);
                    v___x_1357_ = v___x_1337_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___f_1347_);
                    v___x_1357_ = v_reuseFailAlloc_1393_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1358_ = l_ReaderT_instMonad___redArg(v___x_1357_);
                v___x_1359_ = l_StateRefT_x27_instMonad___redArg(v___x_1358_);
                v_toApplicative_1360_ = crate::leanh::lean_ctor_get(v___x_1359_, 0);
                v_isSharedCheck_1391_ = (!crate::leanh::lean_is_exclusive(v___x_1359_)) as u8;
                if v_isSharedCheck_1391_ == 0 {
                    v_unused_1392_ = crate::leanh::lean_ctor_get(v___x_1359_, 1);
                    crate::leanh::lean_dec(v_unused_1392_);
                    v___x_1362_ = v___x_1359_;
                    v_isShared_1363_ = v_isSharedCheck_1391_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1360_);
                    crate::leanh::lean_dec(v___x_1359_);
                    v___x_1362_ = crate::leanh::lean_box(0);
                    v_isShared_1363_ = v_isSharedCheck_1391_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_1364_ = crate::leanh::lean_ctor_get(v_toApplicative_1360_, 0);
                v_toSeq_1365_ = crate::leanh::lean_ctor_get(v_toApplicative_1360_, 2);
                v_toSeqLeft_1366_ = crate::leanh::lean_ctor_get(v_toApplicative_1360_, 3);
                v_toSeqRight_1367_ = crate::leanh::lean_ctor_get(v_toApplicative_1360_, 4);
                v_isSharedCheck_1389_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1360_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v_unused_1390_ = crate::leanh::lean_ctor_get(v_toApplicative_1360_, 1);
                    crate::leanh::lean_dec(v_unused_1390_);
                    v___x_1369_ = v_toApplicative_1360_;
                    v_isShared_1370_ = v_isSharedCheck_1389_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1367_);
                    crate::leanh::lean_inc(v_toSeqLeft_1366_);
                    crate::leanh::lean_inc(v_toSeq_1365_);
                    crate::leanh::lean_inc(v_toFunctor_1364_);
                    crate::leanh::lean_dec(v_toApplicative_1360_);
                    v___x_1369_ = crate::leanh::lean_box(0);
                    v_isShared_1370_ = v_isSharedCheck_1389_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_1371_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0;
                v___f_1372_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1;
                crate::leanh::lean_inc_ref(v_toFunctor_1364_);
                v___f_1373_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1373_, 0, v_toFunctor_1364_);
                v___f_1374_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1374_, 0, v_toFunctor_1364_);
                v___x_1375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1375_, 0, v___f_1373_);
                crate::leanh::lean_ctor_set(v___x_1375_, 1, v___f_1374_);
                v___f_1376_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1376_, 0, v_toSeqRight_1367_);
                v___f_1377_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1377_, 0, v_toSeqLeft_1366_);
                v___f_1378_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1378_, 0, v_toSeq_1365_);
                if v_isShared_1370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1369_, 4, v___f_1376_);
                    crate::leanh::lean_ctor_set(v___x_1369_, 3, v___f_1377_);
                    crate::leanh::lean_ctor_set(v___x_1369_, 2, v___f_1378_);
                    crate::leanh::lean_ctor_set(v___x_1369_, 1, v___f_1371_);
                    crate::leanh::lean_ctor_set(v___x_1369_, 0, v___x_1375_);
                    v___x_1380_ = v___x_1369_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___f_1371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 2, v___f_1378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___f_1377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 4, v___f_1376_);
                    v___x_1380_ = v_reuseFailAlloc_1388_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1362_, 1, v___f_1372_);
                    crate::leanh::lean_ctor_set(v___x_1362_, 0, v___x_1380_);
                    v___x_1382_ = v___x_1362_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1387_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___f_1372_);
                    v___x_1382_ = v_reuseFailAlloc_1387_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1383_ = crate::leanh::lean_box(0);
                v___x_1384_ = l_instInhabitedOfMonad___redArg(v___x_1382_, v___x_1383_);
                v___x_21356__overap_1385_ = lean_panic_fn_borrowed(v___x_1384_, v_msg_1300_);
                crate::leanh::lean_dec(v___x_1384_);
                crate::leanh::lean_inc(v___y_1307_);
                crate::leanh::lean_inc_ref(v___y_1306_);
                crate::leanh::lean_inc(v___y_1305_);
                crate::leanh::lean_inc_ref(v___y_1304_);
                crate::leanh::lean_inc_ref(v___y_1303_);
                crate::leanh::lean_inc(v___y_1302_);
                crate::leanh::lean_inc_ref(v___y_1301_);
                v___x_1386_ = crate::leanh::lean_apply_8(
                    v___x_21356__overap_1385_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1305_,
                    v___y_1306_,
                    v___y_1307_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___boxed(
    mut v_msg_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
    crate::leanh::lean_dec(v___y_1412_);
    crate::leanh::lean_dec_ref(v___y_1411_);
    crate::leanh::lean_dec(v___y_1410_);
    crate::leanh::lean_dec_ref(v___y_1409_);
    crate::leanh::lean_dec_ref(v___y_1408_);
    crate::leanh::lean_dec(v___y_1407_);
    crate::leanh::lean_dec_ref(v___y_1406_);
    return v_res_1414_;
}
pub unsafe fn _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1418_ =
        l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2;
    v___x_1419_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1420_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_1421_ =
        l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1;
    v___x_1422_ =
        l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0;
    v___x_1423_ = l_mkPanicMessageWithDecl(
        v___x_1422_,
        v___x_1421_,
        v___x_1420_,
        v___x_1419_,
        v___x_1418_,
    );
    return v___x_1423_;
}
pub unsafe fn l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(
    mut v_constName_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v_kind_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1433_ = lean_st_ref_get(v___y_1431_);
                v_env_1437_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                crate::leanh::lean_inc_ref(v_env_1437_);
                crate::leanh::lean_dec(v___x_1433_);
                v___x_1438_ = 0;
                v___x_1439_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1437_, v_constName_1424_, v___x_1438_);
                if crate::leanh::lean_obj_tag(v___x_1439_) == 1 {
                    v_val_1440_ = crate::leanh::lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1459_ = (!crate::leanh::lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1459_ == 0 {
                        v___x_1442_ = v___x_1439_;
                        v_isShared_1443_ = v_isSharedCheck_1459_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1440_);
                        crate::leanh::lean_dec(v___x_1439_);
                        v___x_1442_ = crate::leanh::lean_box(0);
                        v_isShared_1443_ = v_isSharedCheck_1459_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1439_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1435_ = crate::leanh::lean_box(0);
                v___x_1436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
                return v___x_1436_;
            }
            2 => {
                v_kind_1444_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_1440_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_1444_ == 6 {
                    v___x_1445_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1440_);
                    if crate::leanh::lean_obj_tag(v___x_1445_) == 6 {
                        v_val_1446_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                        v_isSharedCheck_1456_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1445_)) as u8;
                        if v_isSharedCheck_1456_ == 0 {
                            v___x_1448_ = v___x_1445_;
                            v_isShared_1449_ = v_isSharedCheck_1456_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1446_);
                            crate::leanh::lean_dec(v___x_1445_);
                            v___x_1448_ = crate::leanh::lean_box(0);
                            v_isShared_1449_ = v_isSharedCheck_1456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1445_);
                        crate::leanh::lean_del_object(v___x_1442_);
                        v___x_1457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once), _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3);
                        v___x_1458_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v___x_1457_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
                        return v___x_1458_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1442_);
                    crate::leanh::lean_dec(v_val_1440_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1442_, 0, v_val_1446_);
                    v___x_1451_ = v___x_1442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1449_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1448_, 0);
                    crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1451_);
                    v___x_1453_ = v___x_1448_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___boxed(
    mut v_constName_1460_: *mut crate::leanh::LeanObject,
    mut v___y_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1469_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(
        v_constName_1460_,
        v___y_1461_,
        v___y_1462_,
        v___y_1463_,
        v___y_1464_,
        v___y_1465_,
        v___y_1466_,
        v___y_1467_,
    );
    crate::leanh::lean_dec(v___y_1467_);
    crate::leanh::lean_dec_ref(v___y_1466_);
    crate::leanh::lean_dec(v___y_1465_);
    crate::leanh::lean_dec_ref(v___y_1464_);
    crate::leanh::lean_dec_ref(v___y_1463_);
    crate::leanh::lean_dec(v___y_1462_);
    crate::leanh::lean_dec_ref(v___y_1461_);
    return v_res_1469_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4;
    v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
    return v___x_1478_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6;
    v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
    return v___x_1481_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8;
    v___x_1484_ = l_Lean_stringToMessageData(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12;
    v___x_1489_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_1490_ = crate::leanh::lean_unsigned_to_nat(54);
    v___x_1491_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11;
    v___x_1492_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10;
    v___x_1493_ = l_mkPanicMessageWithDecl(
        v___x_1492_,
        v___x_1491_,
        v___x_1490_,
        v___x_1489_,
        v___x_1488_,
    );
    return v___x_1493_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14;
    v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(
    mut v_e_1497_: *mut crate::leanh::LeanObject,
    mut v_a_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_a_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1512_: u8 = 0;
    let mut v___y_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: u8 = 0;
    let mut v___y_1518_: u8 = 0;
    let mut v___y_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: u8 = 0;
    let mut v___y_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v_levelParams_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1536_: u8 = 0;
    let mut v_unused_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v___y_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: u8 = 0;
    let mut v___y_1554_: u8 = 0;
    let mut v___y_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: u8 = 0;
    let mut v___y_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_a_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: u8 = 0;
    let mut v___y_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: u8 = 0;
    let mut v___y_1599_: u8 = 0;
    let mut v___y_1600_: u8 = 0;
    let mut v___y_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: u8 = 0;
    let mut v___y_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v___y_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1632_: u8 = 0;
    let mut v___y_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1634_: u8 = 0;
    let mut v___y_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1637_: u8 = 0;
    let mut v___y_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1640_: u8 = 0;
    let mut v___y_1641_: u8 = 0;
    let mut v___y_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1667_: u8 = 0;
    let mut v___y_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineDefs_1676_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlinePartial_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v_val_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v_value_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_1693_: u8 = 0;
    let mut v_code_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1704_: u8 = 0;
    let mut v_a_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v_a_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v___y_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: u8 = 0;
    let mut v___y_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_1737_: u8 = 0;
    let mut v_visited_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v_params_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v_a_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_reuseFailAlloc_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut v___y_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: u8 = 0;
    let mut v___y_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_fvarId_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1813_: u8 = 0;
    let mut v___y_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v_val_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_a_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_e_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1849_: u8 = 0;
    let mut v___y_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_a_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut v_a_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_a_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1958_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v_a_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_a_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_us_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mustInline_1512_ = 0;
                if crate::leanh::lean_obj_tag(v_e_1497_) == 3 {
                    v_declName_1864_ = crate::leanh::lean_ctor_get(v_e_1497_, 0);
                    crate::leanh::lean_inc(v_declName_1864_);
                    if crate::leanh::lean_obj_tag(v_declName_1864_) == 1 {
                        v_pre_1865_ = crate::leanh::lean_ctor_get(v_declName_1864_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_1865_) == 0 {
                            v_us_1866_ = crate::leanh::lean_ctor_get(v_e_1497_, 1);
                            crate::leanh::lean_inc(v_us_1866_);
                            v_args_1867_ = crate::leanh::lean_ctor_get(v_e_1497_, 2);
                            crate::leanh::lean_inc_ref(v_args_1867_);
                            crate::leanh::lean_dec_ref_known(v_e_1497_, 3);
                            v_str_1868_ = crate::leanh::lean_ctor_get(v_declName_1864_, 1);
                            v___x_1869_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2;
                            v___x_1870_ = lean_string_dec_eq(v_str_1868_, v___x_1869_);
                            if v___x_1870_ == 0 {
                                v_declName_1664_ = v_declName_1864_;
                                v_us_1665_ = v_us_1866_;
                                v_args_1666_ = v_args_1867_;
                                v_mustInline_1667_ = v_mustInline_1512_;
                                v___y_1668_ = v_a_1498_;
                                v___y_1669_ = v_a_1499_;
                                v___y_1670_ = v_a_1500_;
                                v___y_1671_ = v_a_1501_;
                                v___y_1672_ = v_a_1502_;
                                v___y_1673_ = v_a_1503_;
                                v___y_1674_ = v_a_1504_;
                                state = 21;
                                continue;
                            } else {
                                v___x_1871_ = lean_array_get_size(v_args_1867_);
                                v___x_1872_ = crate::leanh::lean_unsigned_to_nat(2);
                                v_mustInline_1873_ = lean_nat_dec_eq(v___x_1871_, v___x_1872_);
                                if v_mustInline_1873_ == 0 {
                                    v_declName_1664_ = v_declName_1864_;
                                    v_us_1665_ = v_us_1866_;
                                    v_args_1666_ = v_args_1867_;
                                    v_mustInline_1667_ = v_mustInline_1512_;
                                    v___y_1668_ = v_a_1498_;
                                    v___y_1669_ = v_a_1499_;
                                    v___y_1670_ = v_a_1500_;
                                    v___y_1671_ = v_a_1501_;
                                    v___y_1672_ = v_a_1502_;
                                    v___y_1673_ = v_a_1503_;
                                    v___y_1674_ = v_a_1504_;
                                    state = 21;
                                    continue;
                                } else {
                                    v___x_1874_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1875_ =
                                        lean_array_fget_borrowed(v_args_1867_, v___x_1874_);
                                    if crate::leanh::lean_obj_tag(v___x_1875_) == 1 {
                                        crate::leanh::lean_inc_ref(v___x_1875_);
                                        crate::leanh::lean_dec_ref(v_args_1867_);
                                        crate::leanh::lean_dec(v_us_1866_);
                                        crate::leanh::lean_dec_ref_known(v_declName_1864_, 2);
                                        v_fvarId_1876_ =
                                            crate::leanh::lean_ctor_get(v___x_1875_, 0);
                                        crate::leanh::lean_inc_n(v_fvarId_1876_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_1875_, 1);
                                        v___x_1877_ = 0;
                                        v___x_1878_ =
                                            l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
                                                v___x_1877_,
                                                v_fvarId_1876_,
                                                v_a_1502_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_1878_) == 0 {
                                            v_a_1879_ = crate::leanh::lean_ctor_get(v___x_1878_, 0);
                                            crate::leanh::lean_inc(v_a_1879_);
                                            crate::leanh::lean_dec_ref_known(v___x_1878_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_1879_) == 1 {
                                                crate::leanh::lean_dec(v_fvarId_1876_);
                                                v_val_1880_ =
                                                    crate::leanh::lean_ctor_get(v_a_1879_, 0);
                                                crate::leanh::lean_inc(v_val_1880_);
                                                crate::leanh::lean_dec_ref_known(v_a_1879_, 1);
                                                v_fvarId_1881_ =
                                                    crate::leanh::lean_ctor_get(v_val_1880_, 0);
                                                crate::leanh::lean_inc(v_fvarId_1881_);
                                                crate::leanh::lean_dec(v_val_1880_);
                                                v___x_1882_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3;
                                                v_fvarId_1811_ = v_fvarId_1881_;
                                                v_args_1812_ = v___x_1882_;
                                                v_mustInline_1813_ = v_mustInline_1873_;
                                                v___y_1814_ = v_a_1499_;
                                                v___y_1815_ = v_a_1501_;
                                                v___y_1816_ = v_a_1502_;
                                                v___y_1817_ = v_a_1503_;
                                                v___y_1818_ = v_a_1504_;
                                                state = 42;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_a_1879_);
                                                v___x_1883_ =
                                                    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                                                        v___x_1877_,
                                                        v_fvarId_1876_,
                                                        v_a_1502_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_1883_) == 0 {
                                                    v_a_1884_ =
                                                        crate::leanh::lean_ctor_get(v___x_1883_, 0);
                                                    crate::leanh::lean_inc(v_a_1884_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1883_,
                                                        1,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v_a_1884_) == 1 {
                                                        crate::leanh::lean_dec(v_fvarId_1876_);
                                                        v_val_1885_ = crate::leanh::lean_ctor_get(
                                                            v_a_1884_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_1885_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_a_1884_, 1,
                                                        );
                                                        v_value_1886_ = crate::leanh::lean_ctor_get(
                                                            v_val_1885_,
                                                            3,
                                                        );
                                                        crate::leanh::lean_inc(v_value_1886_);
                                                        crate::leanh::lean_dec(v_val_1885_);
                                                        if crate::leanh::lean_obj_tag(v_value_1886_)
                                                            == 3
                                                        {
                                                            v_declName_1887_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_value_1886_,
                                                                    0,
                                                                );
                                                            crate::leanh::lean_inc_n(
                                                                v_declName_1887_,
                                                                2,
                                                            );
                                                            v_us_1888_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_value_1886_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc(v_us_1888_);
                                                            v_args_1889_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v_value_1886_,
                                                                    2,
                                                                );
                                                            crate::leanh::lean_inc_ref(
                                                                v_args_1889_,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_value_1886_,
                                                                3,
                                                            );
                                                            v___x_1890_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(v_declName_1887_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_1890_,
                                                            ) == 0
                                                            {
                                                                v_a_1891_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1890_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_1891_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_1890_,
                                                                    1,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v_a_1891_,
                                                                ) == 0
                                                                {
                                                                    v___x_1892_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_1501_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_1892_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_1893_ = crate::leanh::lean_ctor_get(v___x_1892_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1893_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_1892_, 1);
                                                                        v___x_1894_ = (crate::leanh::lean_unbox(v_a_1893_) as u8);
                                                                        crate::leanh::lean_dec(
                                                                            v_a_1893_,
                                                                        );
                                                                        v___x_1895_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_1887_, v___x_1894_, v_a_1504_);
                                                                        if crate::leanh::lean_obj_tag(v___x_1895_) == 0 {
v_a_1896_ = crate::leanh::lean_ctor_get(v___x_1895_, 0);
crate::leanh::lean_inc(v_a_1896_);
crate::leanh::lean_dec_ref_known(v___x_1895_, 1);
if crate::leanh::lean_obj_tag(v_a_1896_) == 1 {
crate::leanh::lean_dec_ref_known(v_a_1896_, 1);
v_declName_1664_ = v_declName_1887_;
v_us_1665_ = v_us_1888_;
v_args_1666_ = v_args_1889_;
v_mustInline_1667_ = v_mustInline_1873_;
v___y_1668_ = v_a_1498_;
v___y_1669_ = v_a_1499_;
v___y_1670_ = v_a_1500_;
v___y_1671_ = v_a_1501_;
v___y_1672_ = v_a_1502_;
v___y_1673_ = v_a_1503_;
v___y_1674_ = v_a_1504_;
state = 21; continue;
} else {
crate::leanh::lean_dec(v_a_1896_);
crate::leanh::lean_dec_ref(v_args_1889_);
crate::leanh::lean_dec(v_us_1888_);
v___x_1897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5);
v___x_1898_ = l_Lean_MessageData_ofName(v_declName_1887_);
v___x_1899_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
crate::leanh::lean_ctor_set(v___x_1899_, 0, v___x_1897_);
crate::leanh::lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
v___x_1901_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
crate::leanh::lean_ctor_set(v___x_1901_, 0, v___x_1899_);
crate::leanh::lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_1901_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1910_ = (!crate::leanh::lean_is_exclusive(v___x_1902_)) as u8;
if v_isSharedCheck_1910_ == 0 {
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1910_;
state = 49; continue;
} else {
crate::leanh::lean_inc(v_a_1903_);
crate::leanh::lean_dec(v___x_1902_);
v___x_1905_ = crate::leanh::lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
state = 49; continue;
}
}
} else {
crate::leanh::lean_dec_ref(v_args_1889_);
crate::leanh::lean_dec(v_us_1888_);
crate::leanh::lean_dec(v_declName_1887_);
v_a_1911_ = crate::leanh::lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1918_ = (!crate::leanh::lean_is_exclusive(v___x_1895_)) as u8;
if v_isSharedCheck_1918_ == 0 {
v___x_1913_ = v___x_1895_;
v_isShared_1914_ = v_isSharedCheck_1918_;
state = 51; continue;
} else {
crate::leanh::lean_inc(v_a_1911_);
crate::leanh::lean_dec(v___x_1895_);
v___x_1913_ = crate::leanh::lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
state = 51; continue;
}
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_args_1889_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_us_1888_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_declName_1887_,
                                                                        );
                                                                        v_a_1919_ = crate::leanh::lean_ctor_get(v___x_1892_, 0);
                                                                        v_isSharedCheck_1926_ = (!crate::leanh::lean_is_exclusive(v___x_1892_)) as u8;
                                                                        if v_isSharedCheck_1926_
                                                                            == 0
                                                                        {
                                                                            v___x_1921_ =
                                                                                v___x_1892_;
                                                                            v_isShared_1922_ = v_isSharedCheck_1926_;
                                                                            state = 53;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_1919_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_1892_,
                                                                            );
                                                                            v___x_1921_ = crate::leanh::lean_box(0);
                                                                            v_isShared_1922_ = v_isSharedCheck_1926_;
                                                                            state = 53;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref_known(v_a_1891_, 1);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_args_1889_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_us_1888_,
                                                                    );
                                                                    v___x_1927_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9);
                                                                    v___x_1928_ =
                                                                        l_Lean_MessageData_ofName(
                                                                            v_declName_1887_,
                                                                        );
                                                                    v___x_1929_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_1929_,
                                                                        0,
                                                                        v___x_1927_,
                                                                    );
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_1929_,
                                                                        1,
                                                                        v___x_1928_,
                                                                    );
                                                                    v___x_1930_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
                                                                    v___x_1931_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_1931_,
                                                                        0,
                                                                        v___x_1929_,
                                                                    );
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_1931_,
                                                                        1,
                                                                        v___x_1930_,
                                                                    );
                                                                    v___x_1932_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_1931_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                    v_a_1933_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_1932_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_1940_ = (!crate::leanh::lean_is_exclusive(v___x_1932_)) as u8;
                                                                    if v_isSharedCheck_1940_ == 0 {
                                                                        v___x_1935_ = v___x_1932_;
                                                                        v_isShared_1936_ =
                                                                            v_isSharedCheck_1940_;
                                                                        state = 55;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_1933_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_1932_,
                                                                        );
                                                                        v___x_1935_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_1936_ =
                                                                            v_isSharedCheck_1940_;
                                                                        state = 55;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_args_1889_,
                                                                );
                                                                crate::leanh::lean_dec(v_us_1888_);
                                                                crate::leanh::lean_dec(
                                                                    v_declName_1887_,
                                                                );
                                                                v_a_1941_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1890_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1948_ = (!crate::leanh::lean_is_exclusive(v___x_1890_)) as u8;
                                                                if v_isSharedCheck_1948_ == 0 {
                                                                    v___x_1943_ = v___x_1890_;
                                                                    v_isShared_1944_ =
                                                                        v_isSharedCheck_1948_;
                                                                    state = 57;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_1941_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1890_,
                                                                    );
                                                                    v___x_1943_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_1944_ =
                                                                        v_isSharedCheck_1948_;
                                                                    state = 57;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            v_e_1848_ = v_value_1886_;
                                                            v_mustInline_1849_ = v_mustInline_1873_;
                                                            v___y_1850_ = v_a_1498_;
                                                            v___y_1851_ = v_a_1499_;
                                                            v___y_1852_ = v_a_1500_;
                                                            v___y_1853_ = v_a_1501_;
                                                            v___y_1854_ = v_a_1502_;
                                                            v___y_1855_ = v_a_1503_;
                                                            v___y_1856_ = v_a_1504_;
                                                            state = 48;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1884_);
                                                        v___x_1949_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v___x_1877_, v_fvarId_1876_, v_a_1502_);
                                                        crate::leanh::lean_dec(v_fvarId_1876_);
                                                        if crate::leanh::lean_obj_tag(v___x_1949_)
                                                            == 0
                                                        {
                                                            v_a_1950_ = crate::leanh::lean_ctor_get(
                                                                v___x_1949_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_1950_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_1949_,
                                                                1,
                                                            );
                                                            if crate::leanh::lean_obj_tag(v_a_1950_)
                                                                == 0
                                                            {
                                                                v___x_1951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13);
                                                                v___x_1952_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(v___x_1951_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                return v___x_1952_;
                                                            } else {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_a_1950_, 1,
                                                                );
                                                                v___x_1953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15);
                                                                v___x_1954_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_1953_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                v_a_1955_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_1954_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_1962_ = (!crate::leanh::lean_is_exclusive(v___x_1954_)) as u8;
                                                                if v_isSharedCheck_1962_ == 0 {
                                                                    v___x_1957_ = v___x_1954_;
                                                                    v_isShared_1958_ =
                                                                        v_isSharedCheck_1962_;
                                                                    state = 59;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_1955_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_1954_,
                                                                    );
                                                                    v___x_1957_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_1958_ =
                                                                        v_isSharedCheck_1962_;
                                                                    state = 59;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            v_a_1963_ = crate::leanh::lean_ctor_get(
                                                                v___x_1949_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1970_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1949_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1970_ == 0 {
                                                                v___x_1965_ = v___x_1949_;
                                                                v_isShared_1966_ =
                                                                    v_isSharedCheck_1970_;
                                                                state = 61;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1963_);
                                                                crate::leanh::lean_dec(v___x_1949_);
                                                                v___x_1965_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1966_ =
                                                                    v_isSharedCheck_1970_;
                                                                state = 61;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_fvarId_1876_);
                                                    v_a_1971_ =
                                                        crate::leanh::lean_ctor_get(v___x_1883_, 0);
                                                    v_isSharedCheck_1978_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1883_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1978_ == 0 {
                                                        v___x_1973_ = v___x_1883_;
                                                        v_isShared_1974_ = v_isSharedCheck_1978_;
                                                        state = 63;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1971_);
                                                        crate::leanh::lean_dec(v___x_1883_);
                                                        v___x_1973_ = crate::leanh::lean_box(0);
                                                        v_isShared_1974_ = v_isSharedCheck_1978_;
                                                        state = 63;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_fvarId_1876_);
                                            v_a_1979_ = crate::leanh::lean_ctor_get(v___x_1878_, 0);
                                            v_isSharedCheck_1986_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1878_))
                                                    as u8;
                                            if v_isSharedCheck_1986_ == 0 {
                                                v___x_1981_ = v___x_1878_;
                                                v_isShared_1982_ = v_isSharedCheck_1986_;
                                                state = 65;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1979_);
                                                crate::leanh::lean_dec(v___x_1878_);
                                                v___x_1981_ = crate::leanh::lean_box(0);
                                                v_isShared_1982_ = v_isSharedCheck_1986_;
                                                state = 65;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v_declName_1664_ = v_declName_1864_;
                                        v_us_1665_ = v_us_1866_;
                                        v_args_1666_ = v_args_1867_;
                                        v_mustInline_1667_ = v_mustInline_1512_;
                                        v___y_1668_ = v_a_1498_;
                                        v___y_1669_ = v_a_1499_;
                                        v___y_1670_ = v_a_1500_;
                                        v___y_1671_ = v_a_1501_;
                                        v___y_1672_ = v_a_1502_;
                                        v___y_1673_ = v_a_1503_;
                                        v___y_1674_ = v_a_1504_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_us_1987_ = crate::leanh::lean_ctor_get(v_e_1497_, 1);
                            crate::leanh::lean_inc(v_us_1987_);
                            v_args_1988_ = crate::leanh::lean_ctor_get(v_e_1497_, 2);
                            crate::leanh::lean_inc_ref(v_args_1988_);
                            crate::leanh::lean_dec_ref_known(v_e_1497_, 3);
                            v_declName_1664_ = v_declName_1864_;
                            v_us_1665_ = v_us_1987_;
                            v_args_1666_ = v_args_1988_;
                            v_mustInline_1667_ = v_mustInline_1512_;
                            v___y_1668_ = v_a_1498_;
                            v___y_1669_ = v_a_1499_;
                            v___y_1670_ = v_a_1500_;
                            v___y_1671_ = v_a_1501_;
                            v___y_1672_ = v_a_1502_;
                            v___y_1673_ = v_a_1503_;
                            v___y_1674_ = v_a_1504_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_us_1989_ = crate::leanh::lean_ctor_get(v_e_1497_, 1);
                        crate::leanh::lean_inc(v_us_1989_);
                        v_args_1990_ = crate::leanh::lean_ctor_get(v_e_1497_, 2);
                        crate::leanh::lean_inc_ref(v_args_1990_);
                        crate::leanh::lean_dec_ref_known(v_e_1497_, 3);
                        v_declName_1664_ = v_declName_1864_;
                        v_us_1665_ = v_us_1989_;
                        v_args_1666_ = v_args_1990_;
                        v_mustInline_1667_ = v_mustInline_1512_;
                        v___y_1668_ = v_a_1498_;
                        v___y_1669_ = v_a_1499_;
                        v___y_1670_ = v_a_1500_;
                        v___y_1671_ = v_a_1501_;
                        v___y_1672_ = v_a_1502_;
                        v___y_1673_ = v_a_1503_;
                        v___y_1674_ = v_a_1504_;
                        state = 21;
                        continue;
                    }
                } else {
                    v_e_1848_ = v_e_1497_;
                    v_mustInline_1849_ = v_mustInline_1512_;
                    v___y_1850_ = v_a_1498_;
                    v___y_1851_ = v_a_1499_;
                    v___y_1852_ = v_a_1500_;
                    v___y_1853_ = v_a_1501_;
                    v___y_1854_ = v_a_1502_;
                    v___y_1855_ = v_a_1503_;
                    v___y_1856_ = v_a_1504_;
                    state = 48;
                    continue;
                }
            }
            1 => {
                v___x_1507_ = crate::leanh::lean_box(0);
                v___x_1508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1507_);
                return v___x_1508_;
            }
            2 => {
                v___x_1510_ = crate::leanh::lean_box(0);
                v___x_1511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
                return v___x_1511_;
            }
            3 => {
                v___x_1523_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v___y_1522_);
                if crate::leanh::lean_obj_tag(v___x_1523_) == 0 {
                    v_isSharedCheck_1536_ = (!crate::leanh::lean_is_exclusive(v___x_1523_)) as u8;
                    if v_isSharedCheck_1536_ == 0 {
                        v_unused_1537_ = crate::leanh::lean_ctor_get(v___x_1523_, 0);
                        crate::leanh::lean_dec(v_unused_1537_);
                        v___x_1525_ = v___x_1523_;
                        v_isShared_1526_ = v_isSharedCheck_1536_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1523_);
                        v___x_1525_ = crate::leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1536_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1520_);
                    crate::leanh::lean_dec_ref(v___y_1519_);
                    crate::leanh::lean_dec_ref(v___y_1516_);
                    crate::leanh::lean_dec(v___y_1515_);
                    crate::leanh::lean_dec_ref(v___y_1514_);
                    v_a_1538_ = crate::leanh::lean_ctor_get(v___x_1523_, 0);
                    v_isSharedCheck_1545_ = (!crate::leanh::lean_is_exclusive(v___x_1523_)) as u8;
                    if v_isSharedCheck_1545_ == 0 {
                        v___x_1540_ = v___x_1523_;
                        v_isShared_1541_ = v_isSharedCheck_1545_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1538_);
                        crate::leanh::lean_dec(v___x_1523_);
                        v___x_1540_ = crate::leanh::lean_box(0);
                        v_isShared_1541_ = v_isSharedCheck_1545_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v_levelParams_1527_ = crate::leanh::lean_ctor_get(v___y_1520_, 1);
                crate::leanh::lean_inc(v_levelParams_1527_);
                crate::leanh::lean_dec_ref(v___y_1520_);
                crate::leanh::lean_inc_n(v___y_1515_, 2);
                crate::leanh::lean_inc_ref(v___y_1519_);
                v___x_1528_ = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(
                    v___y_1521_,
                    v___y_1519_,
                    v___y_1515_,
                );
                v___x_1529_ = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(
                    v___y_1514_,
                    v_levelParams_1527_,
                    v___y_1515_,
                );
                v___x_1530_ = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(
                    v___y_1519_,
                    v___y_1515_,
                );
                v___x_1531_ = crate::leanh::lean_alloc_ctor(0, 4, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1528_);
                crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1529_);
                crate::leanh::lean_ctor_set(v___x_1531_, 2, v___x_1530_);
                crate::leanh::lean_ctor_set(v___x_1531_, 3, v___y_1516_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_mustInline_1512_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    v___y_1518_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 2) as u32,
                    v___y_1517_,
                );
                v___x_1532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                if v_isShared_1526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1532_);
                    v___x_1534_ = v___x_1525_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
                    v___x_1534_ = v_reuseFailAlloc_1535_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1534_;
            }
            6 => {
                if v_isShared_1541_ == 0 {
                    v___x_1543_ = v___x_1540_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
                    v___x_1543_ = v_reuseFailAlloc_1544_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1543_;
            }
            8 => {
                if v___y_1554_ == 0 {
                    v___y_1514_ = v___y_1547_;
                    v___y_1515_ = v___y_1549_;
                    v___y_1516_ = v___y_1552_;
                    v___y_1517_ = v___y_1553_;
                    v___y_1518_ = v___y_1554_;
                    v___y_1519_ = v___y_1555_;
                    v___y_1520_ = v___y_1557_;
                    v___y_1521_ = v___y_1556_;
                    v___y_1522_ = v___y_1548_;
                    state = 3;
                    continue;
                } else {
                    v___x_1558_ =
                        l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(v___y_1555_);
                    if crate::leanh::lean_obj_tag(v___x_1558_) == 1 {
                        v_val_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1590_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1590_ == 0 {
                            v___x_1561_ = v___x_1558_;
                            v_isShared_1562_ = v_isSharedCheck_1590_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1559_);
                            crate::leanh::lean_dec(v___x_1558_);
                            v___x_1561_ = crate::leanh::lean_box(0);
                            v_isShared_1562_ = v_isSharedCheck_1590_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1558_);
                        crate::leanh::lean_dec_ref(v___y_1557_);
                        crate::leanh::lean_dec_ref(v___y_1555_);
                        crate::leanh::lean_dec_ref(v___y_1552_);
                        crate::leanh::lean_dec(v___y_1549_);
                        crate::leanh::lean_dec_ref(v___y_1547_);
                        v___x_1591_ = crate::leanh::lean_box(0);
                        v___x_1592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1592_, 0, v___x_1591_);
                        return v___x_1592_;
                    }
                }
            }
            9 => {
                v___x_1563_ = lean_array_get_size(v___y_1552_);
                v___x_1564_ = lean_nat_dec_lt(v_val_1559_, v___x_1563_);
                if v___x_1564_ == 0 {
                    crate::leanh::lean_dec(v_val_1559_);
                    crate::leanh::lean_dec_ref(v___y_1557_);
                    crate::leanh::lean_dec_ref(v___y_1555_);
                    crate::leanh::lean_dec_ref(v___y_1552_);
                    crate::leanh::lean_dec(v___y_1549_);
                    crate::leanh::lean_dec_ref(v___y_1547_);
                    v___x_1565_ = crate::leanh::lean_box(0);
                    if v_isShared_1562_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1561_, 0);
                        crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1565_);
                        v___x_1567_ = v___x_1561_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                        v___x_1567_ = v_reuseFailAlloc_1568_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1561_);
                    v___x_1569_ = crate::leanh::lean_box(0);
                    v___x_1570_ = lean_array_get_borrowed(v___x_1569_, v___y_1552_, v_val_1559_);
                    crate::leanh::lean_dec(v_val_1559_);
                    v___x_1571_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(
                        v___x_1570_,
                        v___y_1550_,
                        v___y_1551_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1571_) == 0 {
                        v_a_1572_ = crate::leanh::lean_ctor_get(v___x_1571_, 0);
                        v_isSharedCheck_1581_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1571_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v___x_1574_ = v___x_1571_;
                            v_isShared_1575_ = v_isSharedCheck_1581_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1572_);
                            crate::leanh::lean_dec(v___x_1571_);
                            v___x_1574_ = crate::leanh::lean_box(0);
                            v_isShared_1575_ = v_isSharedCheck_1581_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1557_);
                        crate::leanh::lean_dec_ref(v___y_1555_);
                        crate::leanh::lean_dec_ref(v___y_1552_);
                        crate::leanh::lean_dec(v___y_1549_);
                        crate::leanh::lean_dec_ref(v___y_1547_);
                        v_a_1582_ = crate::leanh::lean_ctor_get(v___x_1571_, 0);
                        v_isSharedCheck_1589_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1571_)) as u8;
                        if v_isSharedCheck_1589_ == 0 {
                            v___x_1584_ = v___x_1571_;
                            v_isShared_1585_ = v_isSharedCheck_1589_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1582_);
                            crate::leanh::lean_dec(v___x_1571_);
                            v___x_1584_ = crate::leanh::lean_box(0);
                            v_isShared_1585_ = v_isSharedCheck_1589_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_1567_;
            }
            11 => {
                v___x_1576_ = (crate::leanh::lean_unbox(v_a_1572_) as u8);
                crate::leanh::lean_dec(v_a_1572_);
                if v___x_1576_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1557_);
                    crate::leanh::lean_dec_ref(v___y_1555_);
                    crate::leanh::lean_dec_ref(v___y_1552_);
                    crate::leanh::lean_dec(v___y_1549_);
                    crate::leanh::lean_dec_ref(v___y_1547_);
                    v___x_1577_ = crate::leanh::lean_box(0);
                    if v_isShared_1575_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1574_, 0, v___x_1577_);
                        v___x_1579_ = v___x_1574_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
                        v___x_1579_ = v_reuseFailAlloc_1580_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1574_);
                    v___y_1514_ = v___y_1547_;
                    v___y_1515_ = v___y_1549_;
                    v___y_1516_ = v___y_1552_;
                    v___y_1517_ = v___y_1553_;
                    v___y_1518_ = v___y_1554_;
                    v___y_1519_ = v___y_1555_;
                    v___y_1520_ = v___y_1557_;
                    v___y_1521_ = v___y_1556_;
                    v___y_1522_ = v___y_1548_;
                    state = 3;
                    continue;
                }
            }
            12 => {
                return v___x_1579_;
            }
            13 => {
                if v_isShared_1585_ == 0 {
                    v___x_1587_ = v___x_1584_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
                    v___x_1587_ = v_reuseFailAlloc_1588_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1587_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v___y_1607_) == 0 {
                    v_a_1608_ = crate::leanh::lean_ctor_get(v___y_1607_, 0);
                    v_isSharedCheck_1620_ = (!crate::leanh::lean_is_exclusive(v___y_1607_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1610_ = v___y_1607_;
                        v_isShared_1611_ = v_isSharedCheck_1620_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1608_);
                        crate::leanh::lean_dec(v___y_1607_);
                        v___x_1610_ = crate::leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1620_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1606_);
                    crate::leanh::lean_dec(v___y_1604_);
                    crate::leanh::lean_dec_ref(v___y_1603_);
                    crate::leanh::lean_dec_ref(v___y_1601_);
                    crate::leanh::lean_dec_ref(v___y_1597_);
                    v_a_1621_ = crate::leanh::lean_ctor_get(v___y_1607_, 0);
                    v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v___y_1607_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___y_1607_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1621_);
                        crate::leanh::lean_dec(v___y_1607_);
                        v___x_1623_ = crate::leanh::lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                v___x_1612_ = (crate::leanh::lean_unbox(v_a_1608_) as u8);
                crate::leanh::lean_dec(v_a_1608_);
                if v___x_1612_ == 0 {
                    crate::leanh::lean_del_object(v___x_1610_);
                    crate::leanh::lean_dec_ref(v___y_1606_);
                    crate::leanh::lean_dec(v___y_1604_);
                    crate::leanh::lean_dec_ref(v___y_1603_);
                    crate::leanh::lean_dec_ref(v___y_1601_);
                    crate::leanh::lean_dec_ref(v___y_1597_);
                    state = 1;
                    continue;
                } else {
                    if v___y_1602_ == 0 {
                        if v___y_1595_ == 0 {
                            v___x_1613_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v___y_1606_);
                            v___x_1614_ = lean_array_get_size(v___y_1597_);
                            v___x_1615_ = lean_nat_dec_lt(v___x_1614_, v___x_1613_);
                            crate::leanh::lean_dec(v___x_1613_);
                            if v___x_1615_ == 0 {
                                crate::leanh::lean_del_object(v___x_1610_);
                                v___y_1547_ = v___y_1603_;
                                v___y_1548_ = v___y_1594_;
                                v___y_1549_ = v___y_1604_;
                                v___y_1550_ = v___y_1605_;
                                v___y_1551_ = v___y_1596_;
                                v___y_1552_ = v___y_1597_;
                                v___y_1553_ = v___y_1598_;
                                v___y_1554_ = v___y_1599_;
                                v___y_1555_ = v___y_1606_;
                                v___y_1556_ = v___y_1600_;
                                v___y_1557_ = v___y_1601_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_1606_);
                                crate::leanh::lean_dec(v___y_1604_);
                                crate::leanh::lean_dec_ref(v___y_1603_);
                                crate::leanh::lean_dec_ref(v___y_1601_);
                                crate::leanh::lean_dec_ref(v___y_1597_);
                                v___x_1616_ = crate::leanh::lean_box(0);
                                if v_isShared_1611_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1616_);
                                    v___x_1618_ = v___x_1610_;
                                    state = 17;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1619_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1619_,
                                        0,
                                        v___x_1616_,
                                    );
                                    v___x_1618_ = v_reuseFailAlloc_1619_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1610_);
                            v___y_1547_ = v___y_1603_;
                            v___y_1548_ = v___y_1594_;
                            v___y_1549_ = v___y_1604_;
                            v___y_1550_ = v___y_1605_;
                            v___y_1551_ = v___y_1596_;
                            v___y_1552_ = v___y_1597_;
                            v___y_1553_ = v___y_1598_;
                            v___y_1554_ = v___y_1599_;
                            v___y_1555_ = v___y_1606_;
                            v___y_1556_ = v___y_1600_;
                            v___y_1557_ = v___y_1601_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1610_);
                        v___y_1547_ = v___y_1603_;
                        v___y_1548_ = v___y_1594_;
                        v___y_1549_ = v___y_1604_;
                        v___y_1550_ = v___y_1605_;
                        v___y_1551_ = v___y_1596_;
                        v___y_1552_ = v___y_1597_;
                        v___y_1553_ = v___y_1598_;
                        v___y_1554_ = v___y_1599_;
                        v___y_1555_ = v___y_1606_;
                        v___y_1556_ = v___y_1600_;
                        v___y_1557_ = v___y_1601_;
                        state = 8;
                        continue;
                    }
                }
            }
            17 => {
                return v___x_1618_;
            }
            18 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1626_;
            }
            20 => {
                if v___y_1641_ == 0 {
                    v___x_1648_ = l_Lean_Compiler_LCNF_inBasePhase___redArg(v___y_1638_);
                    if crate::leanh::lean_obj_tag(v___x_1648_) == 0 {
                        v_a_1649_ = crate::leanh::lean_ctor_get(v___x_1648_, 0);
                        crate::leanh::lean_inc(v_a_1649_);
                        crate::leanh::lean_dec_ref_known(v___x_1648_, 1);
                        v___x_1650_ = (crate::leanh::lean_unbox(v_a_1649_) as u8);
                        crate::leanh::lean_dec(v_a_1649_);
                        if v___x_1650_ == 0 {
                            v___x_1651_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_1635_);
                            crate::leanh::lean_inc_ref(v___y_1644_);
                            crate::leanh::lean_inc(v___y_1643_);
                            crate::leanh::lean_inc_ref(v___y_1638_);
                            crate::leanh::lean_inc_ref(v___y_1647_);
                            crate::leanh::lean_inc(v___y_1633_);
                            crate::leanh::lean_inc_ref(v___y_1645_);
                            v___x_1652_ = crate::leanh::lean_apply_9(
                                v___y_1631_,
                                v___x_1651_,
                                v___y_1645_,
                                v___y_1633_,
                                v___y_1647_,
                                v___y_1638_,
                                v___y_1643_,
                                v___y_1644_,
                                v___y_1635_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_1594_ = v___y_1633_;
                            v___y_1595_ = v___y_1634_;
                            v___y_1596_ = v___y_1635_;
                            v___y_1597_ = v___y_1636_;
                            v___y_1598_ = v___y_1637_;
                            v___y_1599_ = v___y_1632_;
                            v___y_1600_ = v___y_1640_;
                            v___y_1601_ = v___y_1639_;
                            v___y_1602_ = v___y_1641_;
                            v___y_1603_ = v___y_1630_;
                            v___y_1604_ = v___y_1642_;
                            v___y_1605_ = v___y_1643_;
                            v___y_1606_ = v___y_1646_;
                            v___y_1607_ = v___x_1652_;
                            state = 15;
                            continue;
                        } else {
                            v_name_1653_ = crate::leanh::lean_ctor_get(v___y_1639_, 0);
                            v___x_1654_ =
                                l_Lean_Meta_isInstance___redArg(v_name_1653_, v___y_1635_);
                            if crate::leanh::lean_obj_tag(v___x_1654_) == 0 {
                                v_a_1655_ = crate::leanh::lean_ctor_get(v___x_1654_, 0);
                                crate::leanh::lean_inc(v_a_1655_);
                                crate::leanh::lean_dec_ref_known(v___x_1654_, 1);
                                v___x_1656_ = (crate::leanh::lean_unbox(v_a_1655_) as u8);
                                crate::leanh::lean_dec(v_a_1655_);
                                if v___x_1656_ == 0 {
                                    v___x_1657_ = crate::leanh::lean_box(0);
                                    v___x_1658_ =
                                        l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(
                                            v___y_1631_,
                                            v_name_1653_,
                                            v_mustInline_1512_,
                                            v___x_1657_,
                                            v___y_1645_,
                                            v___y_1633_,
                                            v___y_1647_,
                                            v___y_1638_,
                                            v___y_1643_,
                                            v___y_1644_,
                                            v___y_1635_,
                                        );
                                    v___y_1594_ = v___y_1633_;
                                    v___y_1595_ = v___y_1634_;
                                    v___y_1596_ = v___y_1635_;
                                    v___y_1597_ = v___y_1636_;
                                    v___y_1598_ = v___y_1637_;
                                    v___y_1599_ = v___y_1632_;
                                    v___y_1600_ = v___y_1640_;
                                    v___y_1601_ = v___y_1639_;
                                    v___y_1602_ = v___y_1641_;
                                    v___y_1603_ = v___y_1630_;
                                    v___y_1604_ = v___y_1642_;
                                    v___y_1605_ = v___y_1643_;
                                    v___y_1606_ = v___y_1646_;
                                    v___y_1607_ = v___x_1658_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_1659_ =
                                        l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1;
                                    v___x_1660_ = lean_name_eq(v_name_1653_, v___x_1659_);
                                    if v___x_1660_ == 0 {
                                        crate::leanh::lean_dec_ref(v___y_1646_);
                                        crate::leanh::lean_dec(v___y_1642_);
                                        crate::leanh::lean_dec_ref(v___y_1639_);
                                        crate::leanh::lean_dec_ref(v___y_1636_);
                                        crate::leanh::lean_dec_ref(v___y_1631_);
                                        crate::leanh::lean_dec_ref(v___y_1630_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1661_ = crate::leanh::lean_box(0);
                                        v___x_1662_ =
                                            l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(
                                                v___y_1631_,
                                                v_name_1653_,
                                                v_mustInline_1512_,
                                                v___x_1661_,
                                                v___y_1645_,
                                                v___y_1633_,
                                                v___y_1647_,
                                                v___y_1638_,
                                                v___y_1643_,
                                                v___y_1644_,
                                                v___y_1635_,
                                            );
                                        v___y_1594_ = v___y_1633_;
                                        v___y_1595_ = v___y_1634_;
                                        v___y_1596_ = v___y_1635_;
                                        v___y_1597_ = v___y_1636_;
                                        v___y_1598_ = v___y_1637_;
                                        v___y_1599_ = v___y_1632_;
                                        v___y_1600_ = v___y_1640_;
                                        v___y_1601_ = v___y_1639_;
                                        v___y_1602_ = v___y_1641_;
                                        v___y_1603_ = v___y_1630_;
                                        v___y_1604_ = v___y_1642_;
                                        v___y_1605_ = v___y_1643_;
                                        v___y_1606_ = v___y_1646_;
                                        v___y_1607_ = v___x_1662_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___y_1631_);
                                v___y_1594_ = v___y_1633_;
                                v___y_1595_ = v___y_1634_;
                                v___y_1596_ = v___y_1635_;
                                v___y_1597_ = v___y_1636_;
                                v___y_1598_ = v___y_1637_;
                                v___y_1599_ = v___y_1632_;
                                v___y_1600_ = v___y_1640_;
                                v___y_1601_ = v___y_1639_;
                                v___y_1602_ = v___y_1641_;
                                v___y_1603_ = v___y_1630_;
                                v___y_1604_ = v___y_1642_;
                                v___y_1605_ = v___y_1643_;
                                v___y_1606_ = v___y_1646_;
                                v___y_1607_ = v___x_1654_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1631_);
                        v___y_1594_ = v___y_1633_;
                        v___y_1595_ = v___y_1634_;
                        v___y_1596_ = v___y_1635_;
                        v___y_1597_ = v___y_1636_;
                        v___y_1598_ = v___y_1637_;
                        v___y_1599_ = v___y_1632_;
                        v___y_1600_ = v___y_1640_;
                        v___y_1601_ = v___y_1639_;
                        v___y_1602_ = v___y_1641_;
                        v___y_1603_ = v___y_1630_;
                        v___y_1604_ = v___y_1642_;
                        v___y_1605_ = v___y_1643_;
                        v___y_1606_ = v___y_1646_;
                        v___y_1607_ = v___x_1648_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1631_);
                    v___y_1547_ = v___y_1630_;
                    v___y_1548_ = v___y_1633_;
                    v___y_1549_ = v___y_1642_;
                    v___y_1550_ = v___y_1643_;
                    v___y_1551_ = v___y_1635_;
                    v___y_1552_ = v___y_1636_;
                    v___y_1553_ = v___y_1637_;
                    v___y_1554_ = v___y_1632_;
                    v___y_1555_ = v___y_1646_;
                    v___y_1556_ = v___y_1640_;
                    v___y_1557_ = v___y_1639_;
                    state = 8;
                    continue;
                }
            }
            21 => {
                v_config_1675_ = crate::leanh::lean_ctor_get(v___y_1668_, 1);
                v_inlineDefs_1676_ = crate::leanh::lean_ctor_get_uint8(v_config_1675_, 3 as u32);
                if v_inlineDefs_1676_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_1666_);
                    crate::leanh::lean_dec(v_us_1665_);
                    crate::leanh::lean_dec(v_declName_1664_);
                    v___x_1677_ = crate::leanh::lean_box(0);
                    v___x_1678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                    return v___x_1678_;
                } else {
                    v_inlinePartial_1679_ =
                        crate::leanh::lean_ctor_get_uint8(v_config_1675_, 1 as u32);
                    v___x_1680_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_1671_);
                    if crate::leanh::lean_obj_tag(v___x_1680_) == 0 {
                        v_a_1681_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                        crate::leanh::lean_inc(v_a_1681_);
                        crate::leanh::lean_dec_ref_known(v___x_1680_, 1);
                        v___x_1682_ = (crate::leanh::lean_unbox(v_a_1681_) as u8);
                        v___x_1683_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                            v_declName_1664_,
                            v___x_1682_,
                            v___y_1673_,
                            v___y_1674_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1683_) == 0 {
                            v_a_1684_ = crate::leanh::lean_ctor_get(v___x_1683_, 0);
                            v_isSharedCheck_1704_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1683_)) as u8;
                            if v_isSharedCheck_1704_ == 0 {
                                v___x_1686_ = v___x_1683_;
                                v_isShared_1687_ = v_isSharedCheck_1704_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1684_);
                                crate::leanh::lean_dec(v___x_1683_);
                                v___x_1686_ = crate::leanh::lean_box(0);
                                v_isShared_1687_ = v_isSharedCheck_1704_;
                                state = 22;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1681_);
                            crate::leanh::lean_dec_ref(v_args_1666_);
                            crate::leanh::lean_dec(v_us_1665_);
                            v_a_1705_ = crate::leanh::lean_ctor_get(v___x_1683_, 0);
                            v_isSharedCheck_1712_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1683_)) as u8;
                            if v_isSharedCheck_1712_ == 0 {
                                v___x_1707_ = v___x_1683_;
                                v_isShared_1708_ = v_isSharedCheck_1712_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1705_);
                                crate::leanh::lean_dec(v___x_1683_);
                                v___x_1707_ = crate::leanh::lean_box(0);
                                v_isShared_1708_ = v_isSharedCheck_1712_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_1666_);
                        crate::leanh::lean_dec(v_us_1665_);
                        crate::leanh::lean_dec(v_declName_1664_);
                        v_a_1713_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                        v_isSharedCheck_1720_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1680_)) as u8;
                        if v_isSharedCheck_1720_ == 0 {
                            v___x_1715_ = v___x_1680_;
                            v_isShared_1716_ = v_isSharedCheck_1720_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1713_);
                            crate::leanh::lean_dec(v___x_1680_);
                            v___x_1715_ = crate::leanh::lean_box(0);
                            v_isShared_1716_ = v_isSharedCheck_1720_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            22 => {
                if crate::leanh::lean_obj_tag(v_a_1684_) == 1 {
                    v_val_1688_ = crate::leanh::lean_ctor_get(v_a_1684_, 0);
                    crate::leanh::lean_inc(v_val_1688_);
                    crate::leanh::lean_dec_ref_known(v_a_1684_, 1);
                    v___x_1689_ = (crate::leanh::lean_unbox(v_a_1681_) as u8);
                    crate::leanh::lean_dec(v_a_1681_);
                    v___x_1690_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_1689_);
                    if v___x_1690_ == 0 {
                        v_value_1691_ = crate::leanh::lean_ctor_get(v_val_1688_, 1);
                        if crate::leanh::lean_obj_tag(v_value_1691_) == 0 {
                            crate::leanh::lean_del_object(v___x_1686_);
                            v_toSignature_1692_ = crate::leanh::lean_ctor_get(v_val_1688_, 0);
                            crate::leanh::lean_inc_ref(v_toSignature_1692_);
                            v_recursive_1693_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_1688_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            );
                            v_code_1694_ = crate::leanh::lean_ctor_get(v_value_1691_, 0);
                            crate::leanh::lean_inc_ref_n(v_code_1694_, 2);
                            v___x_1695_ =
                                l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_1688_);
                            v___x_1696_ = crate::leanh::lean_box((v___x_1695_) as usize);
                            v___x_1697_ = crate::leanh::lean_box((v_mustInline_1512_) as usize);
                            v___x_1698_ = crate::leanh::lean_box((v_inlineDefs_1676_) as usize);
                            crate::leanh::lean_inc(v_val_1688_);
                            v___f_1699_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                14,
                                5,
                            );
                            crate::leanh::lean_closure_set(v___f_1699_, 0, v_val_1688_);
                            crate::leanh::lean_closure_set(v___f_1699_, 1, v___x_1696_);
                            crate::leanh::lean_closure_set(v___f_1699_, 2, v_code_1694_);
                            crate::leanh::lean_closure_set(v___f_1699_, 3, v___x_1697_);
                            crate::leanh::lean_closure_set(v___f_1699_, 4, v___x_1698_);
                            if v___x_1695_ == 0 {
                                if v_recursive_1693_ == 0 {
                                    v___y_1630_ = v_code_1694_;
                                    v___y_1631_ = v___f_1699_;
                                    v___y_1632_ = v___x_1695_;
                                    v___y_1633_ = v___y_1669_;
                                    v___y_1634_ = v_inlinePartial_1679_;
                                    v___y_1635_ = v___y_1674_;
                                    v___y_1636_ = v_args_1666_;
                                    v___y_1637_ = v_recursive_1693_;
                                    v___y_1638_ = v___y_1671_;
                                    v___y_1639_ = v_toSignature_1692_;
                                    v___y_1640_ = v___x_1690_;
                                    v___y_1641_ = v_mustInline_1667_;
                                    v___y_1642_ = v_us_1665_;
                                    v___y_1643_ = v___y_1672_;
                                    v___y_1644_ = v___y_1673_;
                                    v___y_1645_ = v___y_1668_;
                                    v___y_1646_ = v_val_1688_;
                                    v___y_1647_ = v___y_1670_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___f_1699_);
                                    crate::leanh::lean_dec_ref(v_code_1694_);
                                    crate::leanh::lean_dec_ref(v_toSignature_1692_);
                                    crate::leanh::lean_dec(v_val_1688_);
                                    crate::leanh::lean_dec_ref(v_args_1666_);
                                    crate::leanh::lean_dec(v_us_1665_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_1630_ = v_code_1694_;
                                v___y_1631_ = v___f_1699_;
                                v___y_1632_ = v___x_1695_;
                                v___y_1633_ = v___y_1669_;
                                v___y_1634_ = v_inlinePartial_1679_;
                                v___y_1635_ = v___y_1674_;
                                v___y_1636_ = v_args_1666_;
                                v___y_1637_ = v_recursive_1693_;
                                v___y_1638_ = v___y_1671_;
                                v___y_1639_ = v_toSignature_1692_;
                                v___y_1640_ = v___x_1690_;
                                v___y_1641_ = v_mustInline_1667_;
                                v___y_1642_ = v_us_1665_;
                                v___y_1643_ = v___y_1672_;
                                v___y_1644_ = v___y_1673_;
                                v___y_1645_ = v___y_1668_;
                                v___y_1646_ = v_val_1688_;
                                v___y_1647_ = v___y_1670_;
                                state = 20;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_1688_);
                            crate::leanh::lean_dec_ref(v_args_1666_);
                            crate::leanh::lean_dec(v_us_1665_);
                            v___x_1700_ = crate::leanh::lean_box(0);
                            if v_isShared_1687_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1686_, 0, v___x_1700_);
                                v___x_1702_ = v___x_1686_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1703_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
                                v___x_1702_ = v_reuseFailAlloc_1703_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1688_);
                        crate::leanh::lean_del_object(v___x_1686_);
                        crate::leanh::lean_dec_ref(v_args_1666_);
                        crate::leanh::lean_dec(v_us_1665_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1686_);
                    crate::leanh::lean_dec(v_a_1684_);
                    crate::leanh::lean_dec(v_a_1681_);
                    crate::leanh::lean_dec_ref(v_args_1666_);
                    crate::leanh::lean_dec(v_us_1665_);
                    state = 2;
                    continue;
                }
            }
            23 => {
                return v___x_1702_;
            }
            24 => {
                if v_isShared_1708_ == 0 {
                    v___x_1710_ = v___x_1707_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
                    v___x_1710_ = v_reuseFailAlloc_1711_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1710_;
            }
            26 => {
                if v_isShared_1716_ == 0 {
                    v___x_1718_ = v___x_1715_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
                    v___x_1718_ = v_reuseFailAlloc_1719_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1718_;
            }
            28 => {
                v___x_1731_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v___y_1730_);
                if crate::leanh::lean_obj_tag(v___x_1731_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1731_, 1);
                    v___x_1732_ = lean_st_ref_take(v___y_1730_);
                    v_subst_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                    v_used_1734_ = crate::leanh::lean_ctor_get(v___x_1732_, 1);
                    v_binderRenaming_1735_ = crate::leanh::lean_ctor_get(v___x_1732_, 2);
                    v_funDeclInfoMap_1736_ = crate::leanh::lean_ctor_get(v___x_1732_, 3);
                    v_simplified_1737_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1732_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    v_visited_1738_ = crate::leanh::lean_ctor_get(v___x_1732_, 4);
                    v_inline_1739_ = crate::leanh::lean_ctor_get(v___x_1732_, 5);
                    v_inlineLocal_1740_ = crate::leanh::lean_ctor_get(v___x_1732_, 6);
                    v_isSharedCheck_1771_ = (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1771_ == 0 {
                        v___x_1742_ = v___x_1732_;
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inlineLocal_1740_);
                        crate::leanh::lean_inc(v_inline_1739_);
                        crate::leanh::lean_inc(v_visited_1738_);
                        crate::leanh::lean_inc(v_funDeclInfoMap_1736_);
                        crate::leanh::lean_inc(v_binderRenaming_1735_);
                        crate::leanh::lean_inc(v_used_1734_);
                        crate::leanh::lean_inc(v_subst_1733_);
                        crate::leanh::lean_dec(v___x_1732_);
                        v___x_1742_ = crate::leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 29;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1727_);
                    crate::leanh::lean_dec_ref(v___y_1724_);
                    crate::leanh::lean_dec_ref(v___y_1722_);
                    v_a_1772_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1779_ = (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v___x_1774_ = v___x_1731_;
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1772_);
                        crate::leanh::lean_dec(v___x_1731_);
                        v___x_1774_ = crate::leanh::lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 35;
                        continue;
                    }
                }
            }
            29 => {
                v___x_1744_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1745_ = lean_nat_add(v_inlineLocal_1740_, v___x_1744_);
                crate::leanh::lean_dec(v_inlineLocal_1740_);
                if v_isShared_1743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1742_, 6, v___x_1745_);
                    v___x_1747_ = v___x_1742_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1770_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_subst_1733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_used_1734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_binderRenaming_1735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_funDeclInfoMap_1736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_visited_1738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 5, v_inline_1739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 6, v___x_1745_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1770_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_1737_,
                    );
                    v___x_1747_ = v_reuseFailAlloc_1770_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1748_ = lean_st_ref_set(v___y_1730_, v___x_1747_);
                v___x_1749_ = l_Lean_Compiler_LCNF_getType(
                    v___y_1727_,
                    v___y_1723_,
                    v___y_1726_,
                    v___y_1728_,
                    v___y_1725_,
                );
                if crate::leanh::lean_obj_tag(v___x_1749_) == 0 {
                    v_a_1750_ = crate::leanh::lean_ctor_get(v___x_1749_, 0);
                    v_isSharedCheck_1761_ = (!crate::leanh::lean_is_exclusive(v___x_1749_)) as u8;
                    if v_isSharedCheck_1761_ == 0 {
                        v___x_1752_ = v___x_1749_;
                        v_isShared_1753_ = v_isSharedCheck_1761_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1750_);
                        crate::leanh::lean_dec(v___x_1749_);
                        v___x_1752_ = crate::leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1761_;
                        state = 31;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1724_);
                    crate::leanh::lean_dec_ref(v___y_1722_);
                    v_a_1762_ = crate::leanh::lean_ctor_get(v___x_1749_, 0);
                    v_isSharedCheck_1769_ = (!crate::leanh::lean_is_exclusive(v___x_1749_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1749_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1762_);
                        crate::leanh::lean_dec(v___x_1749_);
                        v___x_1764_ = crate::leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 33;
                        continue;
                    }
                }
            }
            31 => {
                v_params_1754_ = crate::leanh::lean_ctor_get(v___y_1724_, 2);
                crate::leanh::lean_inc_ref(v_params_1754_);
                v_value_1755_ = crate::leanh::lean_ctor_get(v___y_1724_, 4);
                crate::leanh::lean_inc_ref(v_value_1755_);
                crate::leanh::lean_dec_ref(v___y_1724_);
                v___x_1756_ = crate::leanh::lean_alloc_ctor(0, 4, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1756_, 0, v_params_1754_);
                crate::leanh::lean_ctor_set(v___x_1756_, 1, v_value_1755_);
                crate::leanh::lean_ctor_set(v___x_1756_, 2, v_a_1750_);
                crate::leanh::lean_ctor_set(v___x_1756_, 3, v___y_1722_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1756_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_1729_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1756_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
                    v_mustInline_1512_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1756_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 2) as u32,
                    v_mustInline_1512_,
                );
                v___x_1757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                if v_isShared_1753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1752_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1752_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
                    v___x_1759_ = v_reuseFailAlloc_1760_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1759_;
            }
            33 => {
                if v_isShared_1765_ == 0 {
                    v___x_1767_ = v___x_1764_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_1767_;
            }
            35 => {
                if v_isShared_1775_ == 0 {
                    v___x_1777_ = v___x_1774_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
                    v___x_1777_ = v_reuseFailAlloc_1778_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1777_;
            }
            37 => {
                v___x_1790_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(
                    v___y_1783_,
                    v___y_1789_,
                    v___y_1782_,
                );
                if crate::leanh::lean_obj_tag(v___x_1790_) == 0 {
                    v_a_1791_ = crate::leanh::lean_ctor_get(v___x_1790_, 0);
                    v_isSharedCheck_1801_ = (!crate::leanh::lean_is_exclusive(v___x_1790_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1793_ = v___x_1790_;
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1791_);
                        crate::leanh::lean_dec(v___x_1790_);
                        v___x_1793_ = crate::leanh::lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 38;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1784_);
                    crate::leanh::lean_dec_ref(v___y_1783_);
                    crate::leanh::lean_dec_ref(v___y_1781_);
                    v_a_1802_ = crate::leanh::lean_ctor_get(v___x_1790_, 0);
                    v_isSharedCheck_1809_ = (!crate::leanh::lean_is_exclusive(v___x_1790_)) as u8;
                    if v_isSharedCheck_1809_ == 0 {
                        v___x_1804_ = v___x_1790_;
                        v_isShared_1805_ = v_isSharedCheck_1809_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1802_);
                        crate::leanh::lean_dec(v___x_1790_);
                        v___x_1804_ = crate::leanh::lean_box(0);
                        v_isShared_1805_ = v_isSharedCheck_1809_;
                        state = 40;
                        continue;
                    }
                }
            }
            38 => {
                v___x_1795_ = 1;
                if v___y_1787_ == 0 {
                    v___x_1796_ = (crate::leanh::lean_unbox(v_a_1791_) as u8);
                    crate::leanh::lean_dec(v_a_1791_);
                    if v___x_1796_ == 0 {
                        crate::leanh::lean_dec(v___y_1784_);
                        crate::leanh::lean_dec_ref(v___y_1783_);
                        crate::leanh::lean_dec_ref(v___y_1781_);
                        v___x_1797_ = crate::leanh::lean_box(0);
                        if v_isShared_1794_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1793_, 0, v___x_1797_);
                            v___x_1799_ = v___x_1793_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_1800_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
                            v___x_1799_ = v_reuseFailAlloc_1800_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1793_);
                        v___y_1722_ = v___y_1781_;
                        v___y_1723_ = v___y_1782_;
                        v___y_1724_ = v___y_1783_;
                        v___y_1725_ = v___y_1786_;
                        v___y_1726_ = v___y_1785_;
                        v___y_1727_ = v___y_1784_;
                        v___y_1728_ = v___y_1788_;
                        v___y_1729_ = v___x_1795_;
                        v___y_1730_ = v___y_1789_;
                        state = 28;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1793_);
                    crate::leanh::lean_dec(v_a_1791_);
                    v___y_1722_ = v___y_1781_;
                    v___y_1723_ = v___y_1782_;
                    v___y_1724_ = v___y_1783_;
                    v___y_1725_ = v___y_1786_;
                    v___y_1726_ = v___y_1785_;
                    v___y_1727_ = v___y_1784_;
                    v___y_1728_ = v___y_1788_;
                    v___y_1729_ = v___x_1795_;
                    v___y_1730_ = v___y_1789_;
                    state = 28;
                    continue;
                }
            }
            39 => {
                return v___x_1799_;
            }
            40 => {
                if v_isShared_1805_ == 0 {
                    v___x_1807_ = v___x_1804_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1807_;
            }
            42 => {
                v___x_1819_ = 0;
                crate::leanh::lean_inc(v_fvarId_1811_);
                v___x_1820_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
                    v___x_1819_,
                    v_fvarId_1811_,
                    v___y_1816_,
                );
                if crate::leanh::lean_obj_tag(v___x_1820_) == 0 {
                    v_a_1821_ = crate::leanh::lean_ctor_get(v___x_1820_, 0);
                    v_isSharedCheck_1838_ = (!crate::leanh::lean_is_exclusive(v___x_1820_)) as u8;
                    if v_isSharedCheck_1838_ == 0 {
                        v___x_1823_ = v___x_1820_;
                        v_isShared_1824_ = v_isSharedCheck_1838_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1821_);
                        crate::leanh::lean_dec(v___x_1820_);
                        v___x_1823_ = crate::leanh::lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1838_;
                        state = 43;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_1812_);
                    crate::leanh::lean_dec(v_fvarId_1811_);
                    v_a_1839_ = crate::leanh::lean_ctor_get(v___x_1820_, 0);
                    v_isSharedCheck_1846_ = (!crate::leanh::lean_is_exclusive(v___x_1820_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v___x_1841_ = v___x_1820_;
                        v_isShared_1842_ = v_isSharedCheck_1846_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1839_);
                        crate::leanh::lean_dec(v___x_1820_);
                        v___x_1841_ = crate::leanh::lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1846_;
                        state = 46;
                        continue;
                    }
                }
            }
            43 => {
                if crate::leanh::lean_obj_tag(v_a_1821_) == 1 {
                    if v_mustInline_1813_ == 0 {
                        v_val_1825_ = crate::leanh::lean_ctor_get(v_a_1821_, 0);
                        crate::leanh::lean_inc(v_val_1825_);
                        crate::leanh::lean_dec_ref_known(v_a_1821_, 1);
                        v___x_1826_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1827_ = lean_array_get_size(v_args_1812_);
                        v___x_1828_ = lean_nat_dec_lt(v___x_1826_, v___x_1827_);
                        if v___x_1828_ == 0 {
                            crate::leanh::lean_dec(v_val_1825_);
                            crate::leanh::lean_dec_ref(v_args_1812_);
                            crate::leanh::lean_dec(v_fvarId_1811_);
                            v___x_1829_ = crate::leanh::lean_box(0);
                            if v_isShared_1824_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1823_, 0, v___x_1829_);
                                v___x_1831_ = v___x_1823_;
                                state = 44;
                                continue;
                            } else {
                                v_reuseFailAlloc_1832_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                                v___x_1831_ = v_reuseFailAlloc_1832_;
                                state = 44;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1823_);
                            v___y_1781_ = v_args_1812_;
                            v___y_1782_ = v___y_1815_;
                            v___y_1783_ = v_val_1825_;
                            v___y_1784_ = v_fvarId_1811_;
                            v___y_1785_ = v___y_1816_;
                            v___y_1786_ = v___y_1818_;
                            v___y_1787_ = v_mustInline_1813_;
                            v___y_1788_ = v___y_1817_;
                            v___y_1789_ = v___y_1814_;
                            state = 37;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1823_);
                        v_val_1833_ = crate::leanh::lean_ctor_get(v_a_1821_, 0);
                        crate::leanh::lean_inc(v_val_1833_);
                        crate::leanh::lean_dec_ref_known(v_a_1821_, 1);
                        v___y_1781_ = v_args_1812_;
                        v___y_1782_ = v___y_1815_;
                        v___y_1783_ = v_val_1833_;
                        v___y_1784_ = v_fvarId_1811_;
                        v___y_1785_ = v___y_1816_;
                        v___y_1786_ = v___y_1818_;
                        v___y_1787_ = v_mustInline_1813_;
                        v___y_1788_ = v___y_1817_;
                        v___y_1789_ = v___y_1814_;
                        state = 37;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1821_);
                    crate::leanh::lean_dec_ref(v_args_1812_);
                    crate::leanh::lean_dec(v_fvarId_1811_);
                    v___x_1834_ = crate::leanh::lean_box(0);
                    if v_isShared_1824_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1823_, 0, v___x_1834_);
                        v___x_1836_ = v___x_1823_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_1837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
                        v___x_1836_ = v_reuseFailAlloc_1837_;
                        state = 45;
                        continue;
                    }
                }
            }
            44 => {
                return v___x_1831_;
            }
            45 => {
                return v___x_1836_;
            }
            46 => {
                if v_isShared_1842_ == 0 {
                    v___x_1844_ = v___x_1841_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1844_;
            }
            48 => {
                if crate::leanh::lean_obj_tag(v_e_1848_) == 3 {
                    v_declName_1857_ = crate::leanh::lean_ctor_get(v_e_1848_, 0);
                    crate::leanh::lean_inc(v_declName_1857_);
                    v_us_1858_ = crate::leanh::lean_ctor_get(v_e_1848_, 1);
                    crate::leanh::lean_inc(v_us_1858_);
                    v_args_1859_ = crate::leanh::lean_ctor_get(v_e_1848_, 2);
                    crate::leanh::lean_inc_ref(v_args_1859_);
                    crate::leanh::lean_dec_ref_known(v_e_1848_, 3);
                    v_declName_1664_ = v_declName_1857_;
                    v_us_1665_ = v_us_1858_;
                    v_args_1666_ = v_args_1859_;
                    v_mustInline_1667_ = v_mustInline_1849_;
                    v___y_1668_ = v___y_1850_;
                    v___y_1669_ = v___y_1851_;
                    v___y_1670_ = v___y_1852_;
                    v___y_1671_ = v___y_1853_;
                    v___y_1672_ = v___y_1854_;
                    v___y_1673_ = v___y_1855_;
                    v___y_1674_ = v___y_1856_;
                    state = 21;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_e_1848_) == 4 {
                        v_fvarId_1860_ = crate::leanh::lean_ctor_get(v_e_1848_, 0);
                        crate::leanh::lean_inc(v_fvarId_1860_);
                        v_args_1861_ = crate::leanh::lean_ctor_get(v_e_1848_, 1);
                        crate::leanh::lean_inc_ref(v_args_1861_);
                        crate::leanh::lean_dec_ref_known(v_e_1848_, 2);
                        v_fvarId_1811_ = v_fvarId_1860_;
                        v_args_1812_ = v_args_1861_;
                        v_mustInline_1813_ = v_mustInline_1849_;
                        v___y_1814_ = v___y_1851_;
                        v___y_1815_ = v___y_1853_;
                        v___y_1816_ = v___y_1854_;
                        v___y_1817_ = v___y_1855_;
                        v___y_1818_ = v___y_1856_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_e_1848_);
                        v___x_1862_ = crate::leanh::lean_box(0);
                        v___x_1863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
                        return v___x_1863_;
                    }
                }
            }
            49 => {
                if v_isShared_1906_ == 0 {
                    v___x_1908_ = v___x_1905_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
                    v___x_1908_ = v_reuseFailAlloc_1909_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_1908_;
            }
            51 => {
                if v_isShared_1914_ == 0 {
                    v___x_1916_ = v___x_1913_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_1916_;
            }
            53 => {
                if v_isShared_1922_ == 0 {
                    v___x_1924_ = v___x_1921_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_1925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
                    v___x_1924_ = v_reuseFailAlloc_1925_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_1924_;
            }
            55 => {
                if v_isShared_1936_ == 0 {
                    v___x_1938_ = v___x_1935_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_1938_;
            }
            57 => {
                if v_isShared_1944_ == 0 {
                    v___x_1946_ = v___x_1943_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
                    v___x_1946_ = v_reuseFailAlloc_1947_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_1946_;
            }
            59 => {
                if v_isShared_1958_ == 0 {
                    v___x_1960_ = v___x_1957_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_1961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
                    v___x_1960_ = v_reuseFailAlloc_1961_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_1960_;
            }
            61 => {
                if v_isShared_1966_ == 0 {
                    v___x_1968_ = v___x_1965_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_1969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
                    v___x_1968_ = v_reuseFailAlloc_1969_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_1968_;
            }
            63 => {
                if v_isShared_1974_ == 0 {
                    v___x_1976_ = v___x_1973_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
                    v___x_1976_ = v_reuseFailAlloc_1977_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_1976_;
            }
            65 => {
                if v_isShared_1982_ == 0 {
                    v___x_1984_ = v___x_1981_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_1985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
                    v___x_1984_ = v_reuseFailAlloc_1985_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_1984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___boxed(
    mut v_e_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_a_1994_: *mut crate::leanh::LeanObject,
    mut v_a_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(
        v_e_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_,
    );
    crate::leanh::lean_dec(v_a_1998_);
    crate::leanh::lean_dec_ref(v_a_1997_);
    crate::leanh::lean_dec(v_a_1996_);
    crate::leanh::lean_dec_ref(v_a_1995_);
    crate::leanh::lean_dec_ref(v_a_1994_);
    crate::leanh::lean_dec(v_a_1993_);
    crate::leanh::lean_dec_ref(v_a_1992_);
    return v_res_2000_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_;
    v___x_2084_ = 0;
    v___x_2085_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_;
    v___x_2086_ = l_Lean_registerTraceClass(v___x_2083_, v___x_2084_, v___x_2085_);
    return v___x_2086_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2____boxed(
    mut v_a_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2088_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
    return v_res_2088_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
}
