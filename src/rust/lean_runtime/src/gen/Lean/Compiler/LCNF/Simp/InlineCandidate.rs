// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineCandidate
// Imports: Lean.Compiler.LCNF.Simp.SimpM
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override, l_Lean_Name_str___override,
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_8,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed as *const core::ffi::c_void, m_arity: 12, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            105, 110, 115, 116, 68, 101, 99, 105, 100, 97, 98, 108, 101, 69, 113, 66, 111, 111,
            108, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__0_value)
                as *mut LeanObject,
            6289368979427661087 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value: LeanStringObject<44> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            96, 105, 110, 108, 105, 110, 101, 96, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116,
            111, 32, 110, 111, 110, 45, 108, 111, 99, 97, 108, 32, 100, 101, 99, 108, 97, 114, 97,
            116, 105, 111, 110, 32, 39, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            96, 105, 110, 108, 105, 110, 101, 96, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116,
            111, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 39, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            83, 105, 109, 112, 46, 73, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97,
            116, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            83, 105, 109, 112, 46, 105, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97,
            116, 101, 63, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value: LeanStringObject<121> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 121,
        m_capacity: 121,
        m_length: 120,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101,
            97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105,
            109, 112, 46, 73, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101,
            46, 52, 53, 48, 49, 53, 48, 50, 49, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95,
            104, 121, 103, 46, 51, 51, 54, 46, 48, 32, 41, 46, 105, 115, 83, 111, 109, 101, 10, 32,
            32, 32, 32, 32, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            96, 105, 110, 108, 105, 110, 101, 96, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116,
            111, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 115, 32, 105, 110,
            118, 97, 108, 105, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,11260351269579028997 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__2_value) as *mut LeanObject,7114391375504651962 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,12083366481402619969 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [73, 110, 108, 105, 110, 101, 67, 97, 110, 100, 105, 100, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,3196211847899758028 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9036830464040704205 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,16082240727276424632 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,18273738737171653778 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,1953136760100813779 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,11981961001735387515 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,7736829225013705930 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,6854742905612141859 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,1164919087555456622 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,5416371453231879756 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,11551569653759660685 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,322563206818071653 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,13807283630111217176 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,((( 1449551352 as usize) << 1) | 1) as *mut LeanObject,936188780658061096 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,15369283736512935311 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__30_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__31_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,15053872815982515831 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__32_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,14718621728666061922 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(
    mut v_x_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    v_params_1046_ = lean_ctor_get(v_x_1045_, 0);
    v___x_1047_ = lean_array_get_size(v_params_1046_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity___boxed(
    mut v_x_1048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1049_: *mut LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_x_1048_);
    lean_dec_ref(v_x_1048_);
    return v_res_1049_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1050_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__0);
    v___x_1052_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1052_, 0, v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1053_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__1);
    v___x_1054_ = lean_unsigned_to_nat(0);
    v___x_1055_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1055_, 0, v___x_1054_);
    lean_ctor_set(v___x_1055_, 1, v___x_1054_);
    lean_ctor_set(v___x_1055_, 2, v___x_1054_);
    lean_ctor_set(v___x_1055_, 3, v___x_1054_);
    lean_ctor_set(v___x_1055_, 4, v___x_1053_);
    lean_ctor_set(v___x_1055_, 5, v___x_1053_);
    lean_ctor_set(v___x_1055_, 6, v___x_1053_);
    lean_ctor_set(v___x_1055_, 7, v___x_1053_);
    lean_ctor_set(v___x_1055_, 8, v___x_1053_);
    lean_ctor_set(v___x_1055_, 9, v___x_1053_);
    return v___x_1055_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(
    mut v_msg_1056_: *mut LeanObject,
    mut v___y_1057_: *mut LeanObject,
    mut v___y_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v_env_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v___x_1076_: u8 = 0;
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut v_unused_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v_a_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1062_ = lean_ctor_get(v___y_1059_, 2);
                v_ref_1063_ = lean_ctor_get(v___y_1059_, 5);
                v___x_1064_ = lean_st_ref_get(v___y_1060_);
                v___x_1065_ = lean_st_ref_get(v___y_1058_);
                v___x_1066_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1057_);
                if lean_obj_tag(v___x_1066_) == 0 {
                    v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
                    v_isSharedCheck_1089_ = (!lean_is_exclusive(v___x_1066_)) as u8;
                    if v_isSharedCheck_1089_ == 0 {
                        v___x_1069_ = v___x_1066_;
                        v_isShared_1070_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1067_);
                        lean_dec(v___x_1066_);
                        v___x_1069_ = lean_box(0);
                        v_isShared_1070_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1065_);
                    lean_dec(v___x_1064_);
                    lean_dec_ref(v_msg_1056_);
                    v_a_1090_ = lean_ctor_get(v___x_1066_, 0);
                    v_isSharedCheck_1097_ = (!lean_is_exclusive(v___x_1066_)) as u8;
                    if v_isSharedCheck_1097_ == 0 {
                        v___x_1092_ = v___x_1066_;
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1090_);
                        lean_dec(v___x_1066_);
                        v___x_1092_ = lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_1071_ = lean_ctor_get(v___x_1064_, 0);
                lean_inc_ref(v_env_1071_);
                lean_dec(v___x_1064_);
                v_lctx_1072_ = lean_ctor_get(v___x_1065_, 0);
                v_isSharedCheck_1087_ = (!lean_is_exclusive(v___x_1065_)) as u8;
                if v_isSharedCheck_1087_ == 0 {
                    v_unused_1088_ = lean_ctor_get(v___x_1065_, 1);
                    lean_dec(v_unused_1088_);
                    v___x_1074_ = v___x_1065_;
                    v_isShared_1075_ = v_isSharedCheck_1087_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_1072_);
                    lean_dec(v___x_1065_);
                    v___x_1074_ = lean_box(0);
                    v_isShared_1075_ = v_isSharedCheck_1087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1076_ = (lean_unbox(v_a_1067_) as u8);
                lean_dec(v_a_1067_);
                v___x_1077_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1072_, v___x_1076_);
                lean_dec_ref(v_lctx_1072_);
                v___x_1078_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2_once), _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg___closed__2);
                lean_inc_ref(v_options_1062_);
                v___x_1079_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1079_, 0, v_env_1071_);
                lean_ctor_set(v___x_1079_, 1, v___x_1078_);
                lean_ctor_set(v___x_1079_, 2, v___x_1077_);
                lean_ctor_set(v___x_1079_, 3, v_options_1062_);
                if v_isShared_1075_ == 0 {
                    lean_ctor_set_tag(v___x_1074_, 3);
                    lean_ctor_set(v___x_1074_, 1, v_msg_1056_);
                    lean_ctor_set(v___x_1074_, 0, v___x_1079_);
                    v___x_1081_ = v___x_1074_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1079_);
                    lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_msg_1056_);
                    v___x_1081_ = v_reuseFailAlloc_1086_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_1063_);
                v___x_1082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1082_, 0, v_ref_1063_);
                lean_ctor_set(v___x_1082_, 1, v___x_1081_);
                if v_isShared_1070_ == 0 {
                    lean_ctor_set_tag(v___x_1069_, 1);
                    lean_ctor_set(v___x_1069_, 0, v___x_1082_);
                    v___x_1084_ = v___x_1069_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
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
                    v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
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
    mut v_msg_1098_: *mut LeanObject,
    mut v___y_1099_: *mut LeanObject,
    mut v___y_1100_: *mut LeanObject,
    mut v___y_1101_: *mut LeanObject,
    mut v___y_1102_: *mut LeanObject,
    mut v___y_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1104_: *mut LeanObject = core::ptr::null_mut();
    v_res_1104_ =
        l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(
            v_msg_1098_,
            v___y_1099_,
            v___y_1100_,
            v___y_1101_,
            v___y_1102_,
        );
    lean_dec(v___y_1102_);
    lean_dec_ref(v___y_1101_);
    lean_dec(v___y_1100_);
    lean_dec_ref(v___y_1099_);
    return v_res_1104_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1(
    mut v_00_u03b1_1105_: *mut LeanObject,
    mut v_msg_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
    mut v___y_1109_: *mut LeanObject,
    mut v___y_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1116_: *mut LeanObject,
    mut v_msg_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1126_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1124_);
    lean_dec_ref(v___y_1123_);
    lean_dec(v___y_1122_);
    lean_dec_ref(v___y_1121_);
    lean_dec_ref(v___y_1120_);
    lean_dec(v___y_1119_);
    lean_dec_ref(v___y_1118_);
    return v_res_1126_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1127_ = l_instMonadEIO(lean_box(0));
    return v___x_1127_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(
    mut v_msg_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v_toFunctor_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___f_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v_toFunctor_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___f_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_21341__overap_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1199_: u8 = 0;
    let mut v_unused_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_unused_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_unused_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut v_unused_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1141_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
                v___x_1142_ = l_StateRefT_x27_instMonad___redArg(v___x_1141_);
                v_toApplicative_1143_ = lean_ctor_get(v___x_1142_, 0);
                v_isSharedCheck_1207_ = (!lean_is_exclusive(v___x_1142_)) as u8;
                if v_isSharedCheck_1207_ == 0 {
                    v_unused_1208_ = lean_ctor_get(v___x_1142_, 1);
                    lean_dec(v_unused_1208_);
                    v___x_1145_ = v___x_1142_;
                    v_isShared_1146_ = v_isSharedCheck_1207_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1143_);
                    lean_dec(v___x_1142_);
                    v___x_1145_ = lean_box(0);
                    v_isShared_1146_ = v_isSharedCheck_1207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1147_ = lean_ctor_get(v_toApplicative_1143_, 0);
                v_toSeq_1148_ = lean_ctor_get(v_toApplicative_1143_, 2);
                v_toSeqLeft_1149_ = lean_ctor_get(v_toApplicative_1143_, 3);
                v_toSeqRight_1150_ = lean_ctor_get(v_toApplicative_1143_, 4);
                v_isSharedCheck_1205_ = (!lean_is_exclusive(v_toApplicative_1143_)) as u8;
                if v_isSharedCheck_1205_ == 0 {
                    v_unused_1206_ = lean_ctor_get(v_toApplicative_1143_, 1);
                    lean_dec(v_unused_1206_);
                    v___x_1152_ = v_toApplicative_1143_;
                    v_isShared_1153_ = v_isSharedCheck_1205_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1150_);
                    lean_inc(v_toSeqLeft_1149_);
                    lean_inc(v_toSeq_1148_);
                    lean_inc(v_toFunctor_1147_);
                    lean_dec(v_toApplicative_1143_);
                    v___x_1152_ = lean_box(0);
                    v_isShared_1153_ = v_isSharedCheck_1205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1154_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1;
                v___f_1155_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2;
                lean_inc_ref(v_toFunctor_1147_);
                v___f_1156_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1156_, 0, v_toFunctor_1147_);
                v___f_1157_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1157_, 0, v_toFunctor_1147_);
                v___x_1158_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1158_, 0, v___f_1156_);
                lean_ctor_set(v___x_1158_, 1, v___f_1157_);
                v___f_1159_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1159_, 0, v_toSeqRight_1150_);
                v___f_1160_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1160_, 0, v_toSeqLeft_1149_);
                v___f_1161_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1161_, 0, v_toSeq_1148_);
                if v_isShared_1153_ == 0 {
                    lean_ctor_set(v___x_1152_, 4, v___f_1159_);
                    lean_ctor_set(v___x_1152_, 3, v___f_1160_);
                    lean_ctor_set(v___x_1152_, 2, v___f_1161_);
                    lean_ctor_set(v___x_1152_, 1, v___f_1154_);
                    lean_ctor_set(v___x_1152_, 0, v___x_1158_);
                    v___x_1163_ = v___x_1152_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1158_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___f_1154_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 2, v___f_1161_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___f_1160_);
                    lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___f_1159_);
                    v___x_1163_ = v_reuseFailAlloc_1204_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1146_ == 0 {
                    lean_ctor_set(v___x_1145_, 1, v___f_1155_);
                    lean_ctor_set(v___x_1145_, 0, v___x_1163_);
                    v___x_1165_ = v___x_1145_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1163_);
                    lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___f_1155_);
                    v___x_1165_ = v_reuseFailAlloc_1203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1166_ = l_StateRefT_x27_instMonad___redArg(v___x_1165_);
                v_toApplicative_1167_ = lean_ctor_get(v___x_1166_, 0);
                v_isSharedCheck_1201_ = (!lean_is_exclusive(v___x_1166_)) as u8;
                if v_isSharedCheck_1201_ == 0 {
                    v_unused_1202_ = lean_ctor_get(v___x_1166_, 1);
                    lean_dec(v_unused_1202_);
                    v___x_1169_ = v___x_1166_;
                    v_isShared_1170_ = v_isSharedCheck_1201_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1167_);
                    lean_dec(v___x_1166_);
                    v___x_1169_ = lean_box(0);
                    v_isShared_1170_ = v_isSharedCheck_1201_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1171_ = lean_ctor_get(v_toApplicative_1167_, 0);
                v_toSeq_1172_ = lean_ctor_get(v_toApplicative_1167_, 2);
                v_toSeqLeft_1173_ = lean_ctor_get(v_toApplicative_1167_, 3);
                v_toSeqRight_1174_ = lean_ctor_get(v_toApplicative_1167_, 4);
                v_isSharedCheck_1199_ = (!lean_is_exclusive(v_toApplicative_1167_)) as u8;
                if v_isSharedCheck_1199_ == 0 {
                    v_unused_1200_ = lean_ctor_get(v_toApplicative_1167_, 1);
                    lean_dec(v_unused_1200_);
                    v___x_1176_ = v_toApplicative_1167_;
                    v_isShared_1177_ = v_isSharedCheck_1199_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1174_);
                    lean_inc(v_toSeqLeft_1173_);
                    lean_inc(v_toSeq_1172_);
                    lean_inc(v_toFunctor_1171_);
                    lean_dec(v_toApplicative_1167_);
                    v___x_1176_ = lean_box(0);
                    v_isShared_1177_ = v_isSharedCheck_1199_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1178_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3;
                v___f_1179_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4;
                lean_inc_ref(v_toFunctor_1171_);
                v___f_1180_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1180_, 0, v_toFunctor_1171_);
                v___f_1181_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1181_, 0, v_toFunctor_1171_);
                v___x_1182_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1182_, 0, v___f_1180_);
                lean_ctor_set(v___x_1182_, 1, v___f_1181_);
                v___f_1183_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1183_, 0, v_toSeqRight_1174_);
                v___f_1184_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1184_, 0, v_toSeqLeft_1173_);
                v___f_1185_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1185_, 0, v_toSeq_1172_);
                if v_isShared_1177_ == 0 {
                    lean_ctor_set(v___x_1176_, 4, v___f_1183_);
                    lean_ctor_set(v___x_1176_, 3, v___f_1184_);
                    lean_ctor_set(v___x_1176_, 2, v___f_1185_);
                    lean_ctor_set(v___x_1176_, 1, v___f_1178_);
                    lean_ctor_set(v___x_1176_, 0, v___x_1182_);
                    v___x_1187_ = v___x_1176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1182_);
                    lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___f_1178_);
                    lean_ctor_set(v_reuseFailAlloc_1198_, 2, v___f_1185_);
                    lean_ctor_set(v_reuseFailAlloc_1198_, 3, v___f_1184_);
                    lean_ctor_set(v_reuseFailAlloc_1198_, 4, v___f_1183_);
                    v___x_1187_ = v_reuseFailAlloc_1198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1170_ == 0 {
                    lean_ctor_set(v___x_1169_, 1, v___f_1179_);
                    lean_ctor_set(v___x_1169_, 0, v___x_1187_);
                    v___x_1189_ = v___x_1169_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1187_);
                    lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___f_1179_);
                    v___x_1189_ = v_reuseFailAlloc_1197_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1190_ = l_ReaderT_instMonad___redArg(v___x_1189_);
                v___x_1191_ = l_StateRefT_x27_instMonad___redArg(v___x_1190_);
                v___x_1192_ = lean_box(0);
                v___x_1193_ = l_instInhabitedOfMonad___redArg(v___x_1191_, v___x_1192_);
                v___f_1194_ = lean_alloc_closure(
                    l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1194_, 0, v___x_1193_);
                v___x_21341__overap_1195_ = lean_panic_fn_borrowed(v___f_1194_, v_msg_1132_);
                lean_dec_ref(v___f_1194_);
                lean_inc(v___y_1139_);
                lean_inc_ref(v___y_1138_);
                lean_inc(v___y_1137_);
                lean_inc_ref(v___y_1136_);
                lean_inc_ref(v___y_1135_);
                lean_inc(v___y_1134_);
                lean_inc_ref(v___y_1133_);
                v___x_1196_ = lean_apply_8(
                    v___x_21341__overap_1195_,
                    v___y_1133_,
                    v___y_1134_,
                    v___y_1135_,
                    v___y_1136_,
                    v___y_1137_,
                    v___y_1138_,
                    v___y_1139_,
                    lean_box(0),
                );
                return v___x_1196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___boxed(
    mut v_msg_1209_: *mut LeanObject,
    mut v___y_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1218_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1216_);
    lean_dec_ref(v___y_1215_);
    lean_dec(v___y_1214_);
    lean_dec_ref(v___y_1213_);
    lean_dec_ref(v___y_1212_);
    lean_dec(v___y_1211_);
    lean_dec_ref(v___y_1210_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0(
    mut v_val_1219_: *mut LeanObject,
    mut v___x_1220_: u8,
    mut v_code_1221_: *mut LeanObject,
    mut v_mustInline_1222_: u8,
    mut v_inlineDefs_1223_: u8,
    mut v_____r_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
) -> *mut LeanObject {
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
                    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1236_ =
                        l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_1221_, v___y_1228_);
                    return v___x_1236_;
                } else {
                    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1237_ = lean_box((v_mustInline_1222_) as usize);
                    v___x_1238_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
                    return v___x_1238_;
                }
            } else {
                let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
                v___x_1239_ = lean_box((v_inlineDefs_1223_) as usize);
                v___x_1240_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1240_, 0, v___x_1239_);
                return v___x_1240_;
            }
        } else {
            let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
            v___x_1241_ = lean_box((v_inlineDefs_1223_) as usize);
            v___x_1242_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_1242_, 0, v___x_1241_);
            return v___x_1242_;
        }
    } else {
        let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
        v___x_1243_ = lean_box((v_inlineDefs_1223_) as usize);
        v___x_1244_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1244_, 0, v___x_1243_);
        return v___x_1244_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed(
    mut v_val_1245_: *mut LeanObject,
    mut v___x_1246_: *mut LeanObject,
    mut v_code_1247_: *mut LeanObject,
    mut v_mustInline_1248_: *mut LeanObject,
    mut v_inlineDefs_1249_: *mut LeanObject,
    mut v_____r_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_21877__boxed_1259_: u8 = 0;
    let mut v_mustInline_boxed_1260_: u8 = 0;
    let mut v_inlineDefs_boxed_1261_: u8 = 0;
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
    v___x_21877__boxed_1259_ = (lean_unbox(v___x_1246_) as u8);
    v_mustInline_boxed_1260_ = (lean_unbox(v_mustInline_1248_) as u8);
    v_inlineDefs_boxed_1261_ = (lean_unbox(v_inlineDefs_1249_) as u8);
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
    lean_dec(v___y_1257_);
    lean_dec_ref(v___y_1256_);
    lean_dec(v___y_1255_);
    lean_dec_ref(v___y_1254_);
    lean_dec_ref(v___y_1253_);
    lean_dec(v___y_1252_);
    lean_dec_ref(v___y_1251_);
    lean_dec_ref(v_code_1247_);
    lean_dec_ref(v_val_1245_);
    return v_res_1262_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1(
    mut v___f_1264_: *mut LeanObject,
    mut v_name_1265_: *mut LeanObject,
    mut v_mustInline_1266_: u8,
    mut v_____r_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_name_1265_) == 1 {
                    v_str_1279_ = lean_ctor_get(v_name_1265_, 1);
                    v___x_1280_ =
                        l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___closed__0;
                    v___x_1281_ = lean_string_dec_eq(v_str_1279_, v___x_1280_);
                    if v___x_1281_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___f_1264_);
                        v___x_1282_ = lean_box((v_mustInline_1266_) as usize);
                        v___x_1283_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1283_, 0, v___x_1282_);
                        return v___x_1283_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1277_ = lean_box(0);
                lean_inc(v___y_1274_);
                lean_inc_ref(v___y_1273_);
                lean_inc(v___y_1272_);
                lean_inc_ref(v___y_1271_);
                lean_inc_ref(v___y_1270_);
                lean_inc(v___y_1269_);
                lean_inc_ref(v___y_1268_);
                v___x_1278_ = lean_apply_9(
                    v___f_1264_,
                    v___x_1277_,
                    v___y_1268_,
                    v___y_1269_,
                    v___y_1270_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___y_1274_,
                    lean_box(0),
                );
                return v___x_1278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__1___boxed(
    mut v___f_1284_: *mut LeanObject,
    mut v_name_1285_: *mut LeanObject,
    mut v_mustInline_1286_: *mut LeanObject,
    mut v_____r_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
    mut v___y_1289_: *mut LeanObject,
    mut v___y_1290_: *mut LeanObject,
    mut v___y_1291_: *mut LeanObject,
    mut v___y_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mustInline_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_1296_ = (lean_unbox(v_mustInline_1286_) as u8);
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
    lean_dec(v___y_1294_);
    lean_dec_ref(v___y_1293_);
    lean_dec(v___y_1292_);
    lean_dec_ref(v___y_1291_);
    lean_dec_ref(v___y_1290_);
    lean_dec(v___y_1289_);
    lean_dec_ref(v___y_1288_);
    lean_dec(v_name_1285_);
    return v_res_1297_;
}
pub unsafe fn l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(
    mut v_msg_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v_toFunctor_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1321_: u8 = 0;
    let mut v___f_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v_toFunctor_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___f_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1363_: u8 = 0;
    let mut v_toFunctor_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___f_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_21356__overap_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_unused_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1391_: u8 = 0;
    let mut v_unused_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut v_unused_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v_unused_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1401_: u8 = 0;
    let mut v_unused_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut v_unused_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1309_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__0);
                v___x_1310_ = l_StateRefT_x27_instMonad___redArg(v___x_1309_);
                v_toApplicative_1311_ = lean_ctor_get(v___x_1310_, 0);
                v_isSharedCheck_1403_ = (!lean_is_exclusive(v___x_1310_)) as u8;
                if v_isSharedCheck_1403_ == 0 {
                    v_unused_1404_ = lean_ctor_get(v___x_1310_, 1);
                    lean_dec(v_unused_1404_);
                    v___x_1313_ = v___x_1310_;
                    v_isShared_1314_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1311_);
                    lean_dec(v___x_1310_);
                    v___x_1313_ = lean_box(0);
                    v_isShared_1314_ = v_isSharedCheck_1403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1315_ = lean_ctor_get(v_toApplicative_1311_, 0);
                v_toSeq_1316_ = lean_ctor_get(v_toApplicative_1311_, 2);
                v_toSeqLeft_1317_ = lean_ctor_get(v_toApplicative_1311_, 3);
                v_toSeqRight_1318_ = lean_ctor_get(v_toApplicative_1311_, 4);
                v_isSharedCheck_1401_ = (!lean_is_exclusive(v_toApplicative_1311_)) as u8;
                if v_isSharedCheck_1401_ == 0 {
                    v_unused_1402_ = lean_ctor_get(v_toApplicative_1311_, 1);
                    lean_dec(v_unused_1402_);
                    v___x_1320_ = v_toApplicative_1311_;
                    v_isShared_1321_ = v_isSharedCheck_1401_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1318_);
                    lean_inc(v_toSeqLeft_1317_);
                    lean_inc(v_toSeq_1316_);
                    lean_inc(v_toFunctor_1315_);
                    lean_dec(v_toApplicative_1311_);
                    v___x_1320_ = lean_box(0);
                    v_isShared_1321_ = v_isSharedCheck_1401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1322_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__1;
                v___f_1323_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__2;
                lean_inc_ref(v_toFunctor_1315_);
                v___f_1324_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1324_, 0, v_toFunctor_1315_);
                v___f_1325_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1325_, 0, v_toFunctor_1315_);
                v___x_1326_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1326_, 0, v___f_1324_);
                lean_ctor_set(v___x_1326_, 1, v___f_1325_);
                v___f_1327_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1327_, 0, v_toSeqRight_1318_);
                v___f_1328_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1328_, 0, v_toSeqLeft_1317_);
                v___f_1329_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1329_, 0, v_toSeq_1316_);
                if v_isShared_1321_ == 0 {
                    lean_ctor_set(v___x_1320_, 4, v___f_1327_);
                    lean_ctor_set(v___x_1320_, 3, v___f_1328_);
                    lean_ctor_set(v___x_1320_, 2, v___f_1329_);
                    lean_ctor_set(v___x_1320_, 1, v___f_1322_);
                    lean_ctor_set(v___x_1320_, 0, v___x_1326_);
                    v___x_1331_ = v___x_1320_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1326_);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___f_1322_);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 2, v___f_1329_);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 3, v___f_1328_);
                    lean_ctor_set(v_reuseFailAlloc_1400_, 4, v___f_1327_);
                    v___x_1331_ = v_reuseFailAlloc_1400_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1314_ == 0 {
                    lean_ctor_set(v___x_1313_, 1, v___f_1323_);
                    lean_ctor_set(v___x_1313_, 0, v___x_1331_);
                    v___x_1333_ = v___x_1313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1331_);
                    lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___f_1323_);
                    v___x_1333_ = v_reuseFailAlloc_1399_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1334_ = l_StateRefT_x27_instMonad___redArg(v___x_1333_);
                v_toApplicative_1335_ = lean_ctor_get(v___x_1334_, 0);
                v_isSharedCheck_1397_ = (!lean_is_exclusive(v___x_1334_)) as u8;
                if v_isSharedCheck_1397_ == 0 {
                    v_unused_1398_ = lean_ctor_get(v___x_1334_, 1);
                    lean_dec(v_unused_1398_);
                    v___x_1337_ = v___x_1334_;
                    v_isShared_1338_ = v_isSharedCheck_1397_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1335_);
                    lean_dec(v___x_1334_);
                    v___x_1337_ = lean_box(0);
                    v_isShared_1338_ = v_isSharedCheck_1397_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1339_ = lean_ctor_get(v_toApplicative_1335_, 0);
                v_toSeq_1340_ = lean_ctor_get(v_toApplicative_1335_, 2);
                v_toSeqLeft_1341_ = lean_ctor_get(v_toApplicative_1335_, 3);
                v_toSeqRight_1342_ = lean_ctor_get(v_toApplicative_1335_, 4);
                v_isSharedCheck_1395_ = (!lean_is_exclusive(v_toApplicative_1335_)) as u8;
                if v_isSharedCheck_1395_ == 0 {
                    v_unused_1396_ = lean_ctor_get(v_toApplicative_1335_, 1);
                    lean_dec(v_unused_1396_);
                    v___x_1344_ = v_toApplicative_1335_;
                    v_isShared_1345_ = v_isSharedCheck_1395_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1342_);
                    lean_inc(v_toSeqLeft_1341_);
                    lean_inc(v_toSeq_1340_);
                    lean_inc(v_toFunctor_1339_);
                    lean_dec(v_toApplicative_1335_);
                    v___x_1344_ = lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1395_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1346_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__3;
                v___f_1347_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2___closed__4;
                lean_inc_ref(v_toFunctor_1339_);
                v___f_1348_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1348_, 0, v_toFunctor_1339_);
                v___f_1349_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1349_, 0, v_toFunctor_1339_);
                v___x_1350_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1350_, 0, v___f_1348_);
                lean_ctor_set(v___x_1350_, 1, v___f_1349_);
                v___f_1351_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1351_, 0, v_toSeqRight_1342_);
                v___f_1352_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1352_, 0, v_toSeqLeft_1341_);
                v___f_1353_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1353_, 0, v_toSeq_1340_);
                if v_isShared_1345_ == 0 {
                    lean_ctor_set(v___x_1344_, 4, v___f_1351_);
                    lean_ctor_set(v___x_1344_, 3, v___f_1352_);
                    lean_ctor_set(v___x_1344_, 2, v___f_1353_);
                    lean_ctor_set(v___x_1344_, 1, v___f_1346_);
                    lean_ctor_set(v___x_1344_, 0, v___x_1350_);
                    v___x_1355_ = v___x_1344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1350_);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___f_1346_);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 2, v___f_1353_);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___f_1352_);
                    lean_ctor_set(v_reuseFailAlloc_1394_, 4, v___f_1351_);
                    v___x_1355_ = v_reuseFailAlloc_1394_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1338_ == 0 {
                    lean_ctor_set(v___x_1337_, 1, v___f_1347_);
                    lean_ctor_set(v___x_1337_, 0, v___x_1355_);
                    v___x_1357_ = v___x_1337_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1355_);
                    lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___f_1347_);
                    v___x_1357_ = v_reuseFailAlloc_1393_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1358_ = l_ReaderT_instMonad___redArg(v___x_1357_);
                v___x_1359_ = l_StateRefT_x27_instMonad___redArg(v___x_1358_);
                v_toApplicative_1360_ = lean_ctor_get(v___x_1359_, 0);
                v_isSharedCheck_1391_ = (!lean_is_exclusive(v___x_1359_)) as u8;
                if v_isSharedCheck_1391_ == 0 {
                    v_unused_1392_ = lean_ctor_get(v___x_1359_, 1);
                    lean_dec(v_unused_1392_);
                    v___x_1362_ = v___x_1359_;
                    v_isShared_1363_ = v_isSharedCheck_1391_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1360_);
                    lean_dec(v___x_1359_);
                    v___x_1362_ = lean_box(0);
                    v_isShared_1363_ = v_isSharedCheck_1391_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_1364_ = lean_ctor_get(v_toApplicative_1360_, 0);
                v_toSeq_1365_ = lean_ctor_get(v_toApplicative_1360_, 2);
                v_toSeqLeft_1366_ = lean_ctor_get(v_toApplicative_1360_, 3);
                v_toSeqRight_1367_ = lean_ctor_get(v_toApplicative_1360_, 4);
                v_isSharedCheck_1389_ = (!lean_is_exclusive(v_toApplicative_1360_)) as u8;
                if v_isSharedCheck_1389_ == 0 {
                    v_unused_1390_ = lean_ctor_get(v_toApplicative_1360_, 1);
                    lean_dec(v_unused_1390_);
                    v___x_1369_ = v_toApplicative_1360_;
                    v_isShared_1370_ = v_isSharedCheck_1389_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1367_);
                    lean_inc(v_toSeqLeft_1366_);
                    lean_inc(v_toSeq_1365_);
                    lean_inc(v_toFunctor_1364_);
                    lean_dec(v_toApplicative_1360_);
                    v___x_1369_ = lean_box(0);
                    v_isShared_1370_ = v_isSharedCheck_1389_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_1371_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__0;
                v___f_1372_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___closed__1;
                lean_inc_ref(v_toFunctor_1364_);
                v___f_1373_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1373_, 0, v_toFunctor_1364_);
                v___f_1374_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1374_, 0, v_toFunctor_1364_);
                v___x_1375_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1375_, 0, v___f_1373_);
                lean_ctor_set(v___x_1375_, 1, v___f_1374_);
                v___f_1376_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1376_, 0, v_toSeqRight_1367_);
                v___f_1377_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1377_, 0, v_toSeqLeft_1366_);
                v___f_1378_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1378_, 0, v_toSeq_1365_);
                if v_isShared_1370_ == 0 {
                    lean_ctor_set(v___x_1369_, 4, v___f_1376_);
                    lean_ctor_set(v___x_1369_, 3, v___f_1377_);
                    lean_ctor_set(v___x_1369_, 2, v___f_1378_);
                    lean_ctor_set(v___x_1369_, 1, v___f_1371_);
                    lean_ctor_set(v___x_1369_, 0, v___x_1375_);
                    v___x_1380_ = v___x_1369_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1375_);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___f_1371_);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 2, v___f_1378_);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 3, v___f_1377_);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 4, v___f_1376_);
                    v___x_1380_ = v_reuseFailAlloc_1388_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1363_ == 0 {
                    lean_ctor_set(v___x_1362_, 1, v___f_1372_);
                    lean_ctor_set(v___x_1362_, 0, v___x_1380_);
                    v___x_1382_ = v___x_1362_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1380_);
                    lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___f_1372_);
                    v___x_1382_ = v_reuseFailAlloc_1387_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1383_ = lean_box(0);
                v___x_1384_ = l_instInhabitedOfMonad___redArg(v___x_1382_, v___x_1383_);
                v___x_21356__overap_1385_ = lean_panic_fn_borrowed(v___x_1384_, v_msg_1300_);
                lean_dec(v___x_1384_);
                lean_inc(v___y_1307_);
                lean_inc_ref(v___y_1306_);
                lean_inc(v___y_1305_);
                lean_inc_ref(v___y_1304_);
                lean_inc_ref(v___y_1303_);
                lean_inc(v___y_1302_);
                lean_inc_ref(v___y_1301_);
                v___x_1386_ = lean_apply_8(
                    v___x_21356__overap_1385_,
                    v___y_1301_,
                    v___y_1302_,
                    v___y_1303_,
                    v___y_1304_,
                    v___y_1305_,
                    v___y_1306_,
                    v___y_1307_,
                    lean_box(0),
                );
                return v___x_1386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0___boxed(
    mut v_msg_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
    mut v___y_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
    lean_dec(v___y_1412_);
    lean_dec_ref(v___y_1411_);
    lean_dec(v___y_1410_);
    lean_dec_ref(v___y_1409_);
    lean_dec_ref(v___y_1408_);
    lean_dec(v___y_1407_);
    lean_dec_ref(v___y_1406_);
    return v_res_1414_;
}
pub unsafe fn _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1418_ =
        l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__2;
    v___x_1419_ = lean_unsigned_to_nat(11);
    v___x_1420_ = lean_unsigned_to_nat(122);
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
    mut v_constName_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
    mut v___y_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v_kind_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1433_ = lean_st_ref_get(v___y_1431_);
                v_env_1437_ = lean_ctor_get(v___x_1433_, 0);
                lean_inc_ref(v_env_1437_);
                lean_dec(v___x_1433_);
                v___x_1438_ = 0;
                v___x_1439_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1437_, v_constName_1424_, v___x_1438_);
                if lean_obj_tag(v___x_1439_) == 1 {
                    v_val_1440_ = lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1459_ = (!lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1459_ == 0 {
                        v___x_1442_ = v___x_1439_;
                        v_isShared_1443_ = v_isSharedCheck_1459_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1440_);
                        lean_dec(v___x_1439_);
                        v___x_1442_ = lean_box(0);
                        v_isShared_1443_ = v_isSharedCheck_1459_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1439_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1435_ = lean_box(0);
                v___x_1436_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1436_, 0, v___x_1435_);
                return v___x_1436_;
            }
            2 => {
                v_kind_1444_ = lean_ctor_get_uint8(
                    v_val_1440_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_kind_1444_ == 6 {
                    v___x_1445_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1440_);
                    if lean_obj_tag(v___x_1445_) == 6 {
                        v_val_1446_ = lean_ctor_get(v___x_1445_, 0);
                        v_isSharedCheck_1456_ = (!lean_is_exclusive(v___x_1445_)) as u8;
                        if v_isSharedCheck_1456_ == 0 {
                            v___x_1448_ = v___x_1445_;
                            v_isShared_1449_ = v_isSharedCheck_1456_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1446_);
                            lean_dec(v___x_1445_);
                            v___x_1448_ = lean_box(0);
                            v_isShared_1449_ = v_isSharedCheck_1456_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1445_);
                        lean_del_object(v___x_1442_);
                        v___x_1457_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3_once), _init_l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0___closed__3);
                        v___x_1458_ = l_panic___at___00Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0_spec__0(v___x_1457_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
                        return v___x_1458_;
                    }
                } else {
                    lean_del_object(v___x_1442_);
                    lean_dec(v_val_1440_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_1443_ == 0 {
                    lean_ctor_set(v___x_1442_, 0, v_val_1446_);
                    v___x_1451_ = v___x_1442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1449_ == 0 {
                    lean_ctor_set_tag(v___x_1448_, 0);
                    lean_ctor_set(v___x_1448_, 0, v___x_1451_);
                    v___x_1453_ = v___x_1448_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
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
    mut v_constName_1460_: *mut LeanObject,
    mut v___y_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1469_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1467_);
    lean_dec_ref(v___y_1466_);
    lean_dec(v___y_1465_);
    lean_dec_ref(v___y_1464_);
    lean_dec_ref(v___y_1463_);
    lean_dec(v___y_1462_);
    lean_dec_ref(v___y_1461_);
    return v_res_1469_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    v___x_1477_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__4;
    v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
    return v___x_1478_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7() -> *mut LeanObject {
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__6;
    v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
    return v___x_1481_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9() -> *mut LeanObject {
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1483_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__8;
    v___x_1484_ = l_Lean_stringToMessageData(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13() -> *mut LeanObject
{
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___x_1488_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__12;
    v___x_1489_ = lean_unsigned_to_nat(6);
    v___x_1490_ = lean_unsigned_to_nat(54);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15() -> *mut LeanObject
{
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__14;
    v___x_1496_ = l_Lean_stringToMessageData(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(
    mut v_e_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
    mut v_a_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1512_: u8 = 0;
    let mut v___y_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: u8 = 0;
    let mut v___y_1518_: u8 = 0;
    let mut v___y_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: u8 = 0;
    let mut v___y_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v_levelParams_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1536_: u8 = 0;
    let mut v_unused_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1545_: u8 = 0;
    let mut v___y_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1553_: u8 = 0;
    let mut v___y_1554_: u8 = 0;
    let mut v___y_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1556_: u8 = 0;
    let mut v___y_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_a_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1595_: u8 = 0;
    let mut v___y_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: u8 = 0;
    let mut v___y_1599_: u8 = 0;
    let mut v___y_1600_: u8 = 0;
    let mut v___y_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: u8 = 0;
    let mut v___y_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v___y_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1632_: u8 = 0;
    let mut v___y_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1634_: u8 = 0;
    let mut v___y_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1637_: u8 = 0;
    let mut v___y_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1640_: u8 = 0;
    let mut v___y_1641_: u8 = 0;
    let mut v___y_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1667_: u8 = 0;
    let mut v___y_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineDefs_1676_: u8 = 0;
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlinePartial_1679_: u8 = 0;
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v_val_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v_value_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_1693_: u8 = 0;
    let mut v_code_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1704_: u8 = 0;
    let mut v_a_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v_a_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v___y_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: u8 = 0;
    let mut v___y_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simplified_1737_: u8 = 0;
    let mut v_visited_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inline_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v_params_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v_a_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut v___y_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: u8 = 0;
    let mut v___y_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_fvarId_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1813_: u8 = 0;
    let mut v___y_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v_val_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut v_a_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_e_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1849_: u8 = 0;
    let mut v___y_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mustInline_1873_: u8 = 0;
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_a_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut v_a_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_a_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1958_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_a_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v_a_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_a_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_us_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mustInline_1512_ = 0;
                if lean_obj_tag(v_e_1497_) == 3 {
                    v_declName_1864_ = lean_ctor_get(v_e_1497_, 0);
                    lean_inc(v_declName_1864_);
                    if lean_obj_tag(v_declName_1864_) == 1 {
                        v_pre_1865_ = lean_ctor_get(v_declName_1864_, 0);
                        if lean_obj_tag(v_pre_1865_) == 0 {
                            v_us_1866_ = lean_ctor_get(v_e_1497_, 1);
                            lean_inc(v_us_1866_);
                            v_args_1867_ = lean_ctor_get(v_e_1497_, 2);
                            lean_inc_ref(v_args_1867_);
                            lean_dec_ref_known(v_e_1497_, 3);
                            v_str_1868_ = lean_ctor_get(v_declName_1864_, 1);
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
                                v___x_1872_ = lean_unsigned_to_nat(2);
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
                                    v___x_1874_ = lean_unsigned_to_nat(1);
                                    v___x_1875_ =
                                        lean_array_fget_borrowed(v_args_1867_, v___x_1874_);
                                    if lean_obj_tag(v___x_1875_) == 1 {
                                        lean_inc_ref(v___x_1875_);
                                        lean_dec_ref(v_args_1867_);
                                        lean_dec(v_us_1866_);
                                        lean_dec_ref_known(v_declName_1864_, 2);
                                        v_fvarId_1876_ = lean_ctor_get(v___x_1875_, 0);
                                        lean_inc_n(v_fvarId_1876_, 2);
                                        lean_dec_ref_known(v___x_1875_, 1);
                                        v___x_1877_ = 0;
                                        v___x_1878_ =
                                            l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
                                                v___x_1877_,
                                                v_fvarId_1876_,
                                                v_a_1502_,
                                            );
                                        if lean_obj_tag(v___x_1878_) == 0 {
                                            v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
                                            lean_inc(v_a_1879_);
                                            lean_dec_ref_known(v___x_1878_, 1);
                                            if lean_obj_tag(v_a_1879_) == 1 {
                                                lean_dec(v_fvarId_1876_);
                                                v_val_1880_ = lean_ctor_get(v_a_1879_, 0);
                                                lean_inc(v_val_1880_);
                                                lean_dec_ref_known(v_a_1879_, 1);
                                                v_fvarId_1881_ = lean_ctor_get(v_val_1880_, 0);
                                                lean_inc(v_fvarId_1881_);
                                                lean_dec(v_val_1880_);
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
                                                lean_dec(v_a_1879_);
                                                v___x_1883_ =
                                                    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                                                        v___x_1877_,
                                                        v_fvarId_1876_,
                                                        v_a_1502_,
                                                    );
                                                if lean_obj_tag(v___x_1883_) == 0 {
                                                    v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
                                                    lean_inc(v_a_1884_);
                                                    lean_dec_ref_known(v___x_1883_, 1);
                                                    if lean_obj_tag(v_a_1884_) == 1 {
                                                        lean_dec(v_fvarId_1876_);
                                                        v_val_1885_ = lean_ctor_get(v_a_1884_, 0);
                                                        lean_inc(v_val_1885_);
                                                        lean_dec_ref_known(v_a_1884_, 1);
                                                        v_value_1886_ =
                                                            lean_ctor_get(v_val_1885_, 3);
                                                        lean_inc(v_value_1886_);
                                                        lean_dec(v_val_1885_);
                                                        if lean_obj_tag(v_value_1886_) == 3 {
                                                            v_declName_1887_ =
                                                                lean_ctor_get(v_value_1886_, 0);
                                                            lean_inc_n(v_declName_1887_, 2);
                                                            v_us_1888_ =
                                                                lean_ctor_get(v_value_1886_, 1);
                                                            lean_inc(v_us_1888_);
                                                            v_args_1889_ =
                                                                lean_ctor_get(v_value_1886_, 2);
                                                            lean_inc_ref(v_args_1889_);
                                                            lean_dec_ref_known(v_value_1886_, 3);
                                                            v___x_1890_ = l_Lean_isCtor_x3f___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__0(v_declName_1887_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                            if lean_obj_tag(v___x_1890_) == 0 {
                                                                v_a_1891_ =
                                                                    lean_ctor_get(v___x_1890_, 0);
                                                                lean_inc(v_a_1891_);
                                                                lean_dec_ref_known(v___x_1890_, 1);
                                                                if lean_obj_tag(v_a_1891_) == 0 {
                                                                    v___x_1892_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_1501_);
                                                                    if lean_obj_tag(v___x_1892_)
                                                                        == 0
                                                                    {
                                                                        v_a_1893_ = lean_ctor_get(
                                                                            v___x_1892_,
                                                                            0,
                                                                        );
                                                                        lean_inc(v_a_1893_);
                                                                        lean_dec_ref_known(
                                                                            v___x_1892_,
                                                                            1,
                                                                        );
                                                                        v___x_1894_ =
                                                                            (lean_unbox(v_a_1893_)
                                                                                as u8);
                                                                        lean_dec(v_a_1893_);
                                                                        v___x_1895_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_1887_, v___x_1894_, v_a_1504_);
                                                                        if lean_obj_tag(v___x_1895_)
                                                                            == 0
                                                                        {
                                                                            v_a_1896_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1895_,
                                                                                    0,
                                                                                );
                                                                            lean_inc(v_a_1896_);
                                                                            lean_dec_ref_known(
                                                                                v___x_1895_,
                                                                                1,
                                                                            );
                                                                            if lean_obj_tag(
                                                                                v_a_1896_,
                                                                            ) == 1
                                                                            {
                                                                                lean_dec_ref_known(
                                                                                    v_a_1896_, 1,
                                                                                );
                                                                                v_declName_1664_ = v_declName_1887_;
                                                                                v_us_1665_ =
                                                                                    v_us_1888_;
                                                                                v_args_1666_ =
                                                                                    v_args_1889_;
                                                                                v_mustInline_1667_ = v_mustInline_1873_;
                                                                                v___y_1668_ =
                                                                                    v_a_1498_;
                                                                                v___y_1669_ =
                                                                                    v_a_1499_;
                                                                                v___y_1670_ =
                                                                                    v_a_1500_;
                                                                                v___y_1671_ =
                                                                                    v_a_1501_;
                                                                                v___y_1672_ =
                                                                                    v_a_1502_;
                                                                                v___y_1673_ =
                                                                                    v_a_1503_;
                                                                                v___y_1674_ =
                                                                                    v_a_1504_;
                                                                                state = 21;
                                                                                continue;
                                                                            } else {
                                                                                lean_dec(v_a_1896_);
                                                                                lean_dec_ref(
                                                                                    v_args_1889_,
                                                                                );
                                                                                lean_dec(
                                                                                    v_us_1888_,
                                                                                );
                                                                                v___x_1897_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__5);
                                                                                v___x_1898_ = l_Lean_MessageData_ofName(v_declName_1887_);
                                                                                v___x_1899_ =
                                                                                    lean_alloc_ctor(
                                                                                        7,
                                                                                        2,
                                                                                        (0) as u32,
                                                                                    );
                                                                                lean_ctor_set(
                                                                                    v___x_1899_,
                                                                                    0,
                                                                                    v___x_1897_,
                                                                                );
                                                                                lean_ctor_set(
                                                                                    v___x_1899_,
                                                                                    1,
                                                                                    v___x_1898_,
                                                                                );
                                                                                v___x_1900_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
                                                                                v___x_1901_ =
                                                                                    lean_alloc_ctor(
                                                                                        7,
                                                                                        2,
                                                                                        (0) as u32,
                                                                                    );
                                                                                lean_ctor_set(
                                                                                    v___x_1901_,
                                                                                    0,
                                                                                    v___x_1899_,
                                                                                );
                                                                                lean_ctor_set(
                                                                                    v___x_1901_,
                                                                                    1,
                                                                                    v___x_1900_,
                                                                                );
                                                                                v___x_1902_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_1901_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                                v_a_1903_ =
                                                                                    lean_ctor_get(
                                                                                        v___x_1902_,
                                                                                        0,
                                                                                    );
                                                                                v_isSharedCheck_1910_ = (!lean_is_exclusive(v___x_1902_)) as u8;
                                                                                if v_isSharedCheck_1910_ == 0 {
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1910_;
state = 49; continue;
} else {
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
state = 49; continue;
}
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_args_1889_,
                                                                            );
                                                                            lean_dec(v_us_1888_);
                                                                            lean_dec(
                                                                                v_declName_1887_,
                                                                            );
                                                                            v_a_1911_ =
                                                                                lean_ctor_get(
                                                                                    v___x_1895_,
                                                                                    0,
                                                                                );
                                                                            v_isSharedCheck_1918_ =
                                                                                (!lean_is_exclusive(
                                                                                    v___x_1895_,
                                                                                ))
                                                                                    as u8;
                                                                            if v_isSharedCheck_1918_
                                                                                == 0
                                                                            {
                                                                                v___x_1913_ =
                                                                                    v___x_1895_;
                                                                                v_isShared_1914_ = v_isSharedCheck_1918_;
                                                                                state = 51;
                                                                                continue;
                                                                            } else {
                                                                                lean_inc(v_a_1911_);
                                                                                lean_dec(
                                                                                    v___x_1895_,
                                                                                );
                                                                                v___x_1913_ =
                                                                                    lean_box(0);
                                                                                v_isShared_1914_ = v_isSharedCheck_1918_;
                                                                                state = 51;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_args_1889_);
                                                                        lean_dec(v_us_1888_);
                                                                        lean_dec(v_declName_1887_);
                                                                        v_a_1919_ = lean_ctor_get(
                                                                            v___x_1892_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_1926_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_1892_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_1926_
                                                                            == 0
                                                                        {
                                                                            v___x_1921_ =
                                                                                v___x_1892_;
                                                                            v_isShared_1922_ = v_isSharedCheck_1926_;
                                                                            state = 53;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_1919_);
                                                                            lean_dec(v___x_1892_);
                                                                            v___x_1921_ =
                                                                                lean_box(0);
                                                                            v_isShared_1922_ = v_isSharedCheck_1926_;
                                                                            state = 53;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref_known(
                                                                        v_a_1891_, 1,
                                                                    );
                                                                    lean_dec_ref(v_args_1889_);
                                                                    lean_dec(v_us_1888_);
                                                                    v___x_1927_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__9);
                                                                    v___x_1928_ =
                                                                        l_Lean_MessageData_ofName(
                                                                            v_declName_1887_,
                                                                        );
                                                                    v___x_1929_ = lean_alloc_ctor(
                                                                        7,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                    lean_ctor_set(
                                                                        v___x_1929_,
                                                                        0,
                                                                        v___x_1927_,
                                                                    );
                                                                    lean_ctor_set(
                                                                        v___x_1929_,
                                                                        1,
                                                                        v___x_1928_,
                                                                    );
                                                                    v___x_1930_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__7);
                                                                    v___x_1931_ = lean_alloc_ctor(
                                                                        7,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                    lean_ctor_set(
                                                                        v___x_1931_,
                                                                        0,
                                                                        v___x_1929_,
                                                                    );
                                                                    lean_ctor_set(
                                                                        v___x_1931_,
                                                                        1,
                                                                        v___x_1930_,
                                                                    );
                                                                    v___x_1932_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_1931_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                    v_a_1933_ = lean_ctor_get(
                                                                        v___x_1932_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_1940_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_1932_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_1940_ == 0 {
                                                                        v___x_1935_ = v___x_1932_;
                                                                        v_isShared_1936_ =
                                                                            v_isSharedCheck_1940_;
                                                                        state = 55;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_1933_);
                                                                        lean_dec(v___x_1932_);
                                                                        v___x_1935_ = lean_box(0);
                                                                        v_isShared_1936_ =
                                                                            v_isSharedCheck_1940_;
                                                                        state = 55;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_args_1889_);
                                                                lean_dec(v_us_1888_);
                                                                lean_dec(v_declName_1887_);
                                                                v_a_1941_ =
                                                                    lean_ctor_get(v___x_1890_, 0);
                                                                v_isSharedCheck_1948_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_1890_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_1948_ == 0 {
                                                                    v___x_1943_ = v___x_1890_;
                                                                    v_isShared_1944_ =
                                                                        v_isSharedCheck_1948_;
                                                                    state = 57;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_1941_);
                                                                    lean_dec(v___x_1890_);
                                                                    v___x_1943_ = lean_box(0);
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
                                                        lean_dec(v_a_1884_);
                                                        v___x_1949_ = l_Lean_Compiler_LCNF_findParam_x3f___redArg(v___x_1877_, v_fvarId_1876_, v_a_1502_);
                                                        lean_dec(v_fvarId_1876_);
                                                        if lean_obj_tag(v___x_1949_) == 0 {
                                                            v_a_1950_ =
                                                                lean_ctor_get(v___x_1949_, 0);
                                                            lean_inc(v_a_1950_);
                                                            lean_dec_ref_known(v___x_1949_, 1);
                                                            if lean_obj_tag(v_a_1950_) == 0 {
                                                                v___x_1951_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__13);
                                                                v___x_1952_ = l_panic___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__2(v___x_1951_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                return v___x_1952_;
                                                            } else {
                                                                lean_dec_ref_known(v_a_1950_, 1);
                                                                v___x_1953_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15_once), _init_l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___closed__15);
                                                                v___x_1954_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_Simp_inlineCandidate_x3f_spec__1___redArg(v___x_1953_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
                                                                v_a_1955_ =
                                                                    lean_ctor_get(v___x_1954_, 0);
                                                                v_isSharedCheck_1962_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_1954_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_1962_ == 0 {
                                                                    v___x_1957_ = v___x_1954_;
                                                                    v_isShared_1958_ =
                                                                        v_isSharedCheck_1962_;
                                                                    state = 59;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_1955_);
                                                                    lean_dec(v___x_1954_);
                                                                    v___x_1957_ = lean_box(0);
                                                                    v_isShared_1958_ =
                                                                        v_isSharedCheck_1962_;
                                                                    state = 59;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            v_a_1963_ =
                                                                lean_ctor_get(v___x_1949_, 0);
                                                            v_isSharedCheck_1970_ =
                                                                (!lean_is_exclusive(v___x_1949_))
                                                                    as u8;
                                                            if v_isSharedCheck_1970_ == 0 {
                                                                v___x_1965_ = v___x_1949_;
                                                                v_isShared_1966_ =
                                                                    v_isSharedCheck_1970_;
                                                                state = 61;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_1963_);
                                                                lean_dec(v___x_1949_);
                                                                v___x_1965_ = lean_box(0);
                                                                v_isShared_1966_ =
                                                                    v_isSharedCheck_1970_;
                                                                state = 61;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_fvarId_1876_);
                                                    v_a_1971_ = lean_ctor_get(v___x_1883_, 0);
                                                    v_isSharedCheck_1978_ =
                                                        (!lean_is_exclusive(v___x_1883_)) as u8;
                                                    if v_isSharedCheck_1978_ == 0 {
                                                        v___x_1973_ = v___x_1883_;
                                                        v_isShared_1974_ = v_isSharedCheck_1978_;
                                                        state = 63;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_1971_);
                                                        lean_dec(v___x_1883_);
                                                        v___x_1973_ = lean_box(0);
                                                        v_isShared_1974_ = v_isSharedCheck_1978_;
                                                        state = 63;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec(v_fvarId_1876_);
                                            v_a_1979_ = lean_ctor_get(v___x_1878_, 0);
                                            v_isSharedCheck_1986_ =
                                                (!lean_is_exclusive(v___x_1878_)) as u8;
                                            if v_isSharedCheck_1986_ == 0 {
                                                v___x_1981_ = v___x_1878_;
                                                v_isShared_1982_ = v_isSharedCheck_1986_;
                                                state = 65;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1979_);
                                                lean_dec(v___x_1878_);
                                                v___x_1981_ = lean_box(0);
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
                            v_us_1987_ = lean_ctor_get(v_e_1497_, 1);
                            lean_inc(v_us_1987_);
                            v_args_1988_ = lean_ctor_get(v_e_1497_, 2);
                            lean_inc_ref(v_args_1988_);
                            lean_dec_ref_known(v_e_1497_, 3);
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
                        v_us_1989_ = lean_ctor_get(v_e_1497_, 1);
                        lean_inc(v_us_1989_);
                        v_args_1990_ = lean_ctor_get(v_e_1497_, 2);
                        lean_inc_ref(v_args_1990_);
                        lean_dec_ref_known(v_e_1497_, 3);
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
                v___x_1507_ = lean_box(0);
                v___x_1508_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1508_, 0, v___x_1507_);
                return v___x_1508_;
            }
            2 => {
                v___x_1510_ = lean_box(0);
                v___x_1511_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1511_, 0, v___x_1510_);
                return v___x_1511_;
            }
            3 => {
                v___x_1523_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v___y_1522_);
                if lean_obj_tag(v___x_1523_) == 0 {
                    v_isSharedCheck_1536_ = (!lean_is_exclusive(v___x_1523_)) as u8;
                    if v_isSharedCheck_1536_ == 0 {
                        v_unused_1537_ = lean_ctor_get(v___x_1523_, 0);
                        lean_dec(v_unused_1537_);
                        v___x_1525_ = v___x_1523_;
                        v_isShared_1526_ = v_isSharedCheck_1536_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_1523_);
                        v___x_1525_ = lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1536_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_1520_);
                    lean_dec_ref(v___y_1519_);
                    lean_dec_ref(v___y_1516_);
                    lean_dec(v___y_1515_);
                    lean_dec_ref(v___y_1514_);
                    v_a_1538_ = lean_ctor_get(v___x_1523_, 0);
                    v_isSharedCheck_1545_ = (!lean_is_exclusive(v___x_1523_)) as u8;
                    if v_isSharedCheck_1545_ == 0 {
                        v___x_1540_ = v___x_1523_;
                        v_isShared_1541_ = v_isSharedCheck_1545_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1538_);
                        lean_dec(v___x_1523_);
                        v___x_1540_ = lean_box(0);
                        v_isShared_1541_ = v_isSharedCheck_1545_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v_levelParams_1527_ = lean_ctor_get(v___y_1520_, 1);
                lean_inc(v_levelParams_1527_);
                lean_dec_ref(v___y_1520_);
                lean_inc_n(v___y_1515_, 2);
                lean_inc_ref(v___y_1519_);
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
                v___x_1531_ = lean_alloc_ctor(0, 4, (3) as u32);
                lean_ctor_set(v___x_1531_, 0, v___x_1528_);
                lean_ctor_set(v___x_1531_, 1, v___x_1529_);
                lean_ctor_set(v___x_1531_, 2, v___x_1530_);
                lean_ctor_set(v___x_1531_, 3, v___y_1516_);
                lean_ctor_set_uint8(
                    v___x_1531_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_mustInline_1512_,
                );
                lean_ctor_set_uint8(
                    v___x_1531_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    v___y_1518_,
                );
                lean_ctor_set_uint8(
                    v___x_1531_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 2) as u32,
                    v___y_1517_,
                );
                v___x_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                if v_isShared_1526_ == 0 {
                    lean_ctor_set(v___x_1525_, 0, v___x_1532_);
                    v___x_1534_ = v___x_1525_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
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
                    v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
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
                    if lean_obj_tag(v___x_1558_) == 1 {
                        v_val_1559_ = lean_ctor_get(v___x_1558_, 0);
                        v_isSharedCheck_1590_ = (!lean_is_exclusive(v___x_1558_)) as u8;
                        if v_isSharedCheck_1590_ == 0 {
                            v___x_1561_ = v___x_1558_;
                            v_isShared_1562_ = v_isSharedCheck_1590_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_val_1559_);
                            lean_dec(v___x_1558_);
                            v___x_1561_ = lean_box(0);
                            v_isShared_1562_ = v_isSharedCheck_1590_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1558_);
                        lean_dec_ref(v___y_1557_);
                        lean_dec_ref(v___y_1555_);
                        lean_dec_ref(v___y_1552_);
                        lean_dec(v___y_1549_);
                        lean_dec_ref(v___y_1547_);
                        v___x_1591_ = lean_box(0);
                        v___x_1592_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1592_, 0, v___x_1591_);
                        return v___x_1592_;
                    }
                }
            }
            9 => {
                v___x_1563_ = lean_array_get_size(v___y_1552_);
                v___x_1564_ = lean_nat_dec_lt(v_val_1559_, v___x_1563_);
                if v___x_1564_ == 0 {
                    lean_dec(v_val_1559_);
                    lean_dec_ref(v___y_1557_);
                    lean_dec_ref(v___y_1555_);
                    lean_dec_ref(v___y_1552_);
                    lean_dec(v___y_1549_);
                    lean_dec_ref(v___y_1547_);
                    v___x_1565_ = lean_box(0);
                    if v_isShared_1562_ == 0 {
                        lean_ctor_set_tag(v___x_1561_, 0);
                        lean_ctor_set(v___x_1561_, 0, v___x_1565_);
                        v___x_1567_ = v___x_1561_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
                        v___x_1567_ = v_reuseFailAlloc_1568_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1561_);
                    v___x_1569_ = lean_box(0);
                    v___x_1570_ = lean_array_get_borrowed(v___x_1569_, v___y_1552_, v_val_1559_);
                    lean_dec(v_val_1559_);
                    v___x_1571_ = l_Lean_Compiler_LCNF_Arg_isConstructorApp___redArg(
                        v___x_1570_,
                        v___y_1550_,
                        v___y_1551_,
                    );
                    if lean_obj_tag(v___x_1571_) == 0 {
                        v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
                        v_isSharedCheck_1581_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v___x_1574_ = v___x_1571_;
                            v_isShared_1575_ = v_isSharedCheck_1581_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_1572_);
                            lean_dec(v___x_1571_);
                            v___x_1574_ = lean_box(0);
                            v_isShared_1575_ = v_isSharedCheck_1581_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___y_1557_);
                        lean_dec_ref(v___y_1555_);
                        lean_dec_ref(v___y_1552_);
                        lean_dec(v___y_1549_);
                        lean_dec_ref(v___y_1547_);
                        v_a_1582_ = lean_ctor_get(v___x_1571_, 0);
                        v_isSharedCheck_1589_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                        if v_isSharedCheck_1589_ == 0 {
                            v___x_1584_ = v___x_1571_;
                            v_isShared_1585_ = v_isSharedCheck_1589_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_1582_);
                            lean_dec(v___x_1571_);
                            v___x_1584_ = lean_box(0);
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
                v___x_1576_ = (lean_unbox(v_a_1572_) as u8);
                lean_dec(v_a_1572_);
                if v___x_1576_ == 0 {
                    lean_dec_ref(v___y_1557_);
                    lean_dec_ref(v___y_1555_);
                    lean_dec_ref(v___y_1552_);
                    lean_dec(v___y_1549_);
                    lean_dec_ref(v___y_1547_);
                    v___x_1577_ = lean_box(0);
                    if v_isShared_1575_ == 0 {
                        lean_ctor_set(v___x_1574_, 0, v___x_1577_);
                        v___x_1579_ = v___x_1574_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
                        v___x_1579_ = v_reuseFailAlloc_1580_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1574_);
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
                    v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
                    v___x_1587_ = v_reuseFailAlloc_1588_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1587_;
            }
            15 => {
                if lean_obj_tag(v___y_1607_) == 0 {
                    v_a_1608_ = lean_ctor_get(v___y_1607_, 0);
                    v_isSharedCheck_1620_ = (!lean_is_exclusive(v___y_1607_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1610_ = v___y_1607_;
                        v_isShared_1611_ = v_isSharedCheck_1620_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_1608_);
                        lean_dec(v___y_1607_);
                        v___x_1610_ = lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1620_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_1606_);
                    lean_dec(v___y_1604_);
                    lean_dec_ref(v___y_1603_);
                    lean_dec_ref(v___y_1601_);
                    lean_dec_ref(v___y_1597_);
                    v_a_1621_ = lean_ctor_get(v___y_1607_, 0);
                    v_isSharedCheck_1628_ = (!lean_is_exclusive(v___y_1607_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___y_1607_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_1621_);
                        lean_dec(v___y_1607_);
                        v___x_1623_ = lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                v___x_1612_ = (lean_unbox(v_a_1608_) as u8);
                lean_dec(v_a_1608_);
                if v___x_1612_ == 0 {
                    lean_del_object(v___x_1610_);
                    lean_dec_ref(v___y_1606_);
                    lean_dec(v___y_1604_);
                    lean_dec_ref(v___y_1603_);
                    lean_dec_ref(v___y_1601_);
                    lean_dec_ref(v___y_1597_);
                    state = 1;
                    continue;
                } else {
                    if v___y_1602_ == 0 {
                        if v___y_1595_ == 0 {
                            v___x_1613_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v___y_1606_);
                            v___x_1614_ = lean_array_get_size(v___y_1597_);
                            v___x_1615_ = lean_nat_dec_lt(v___x_1614_, v___x_1613_);
                            lean_dec(v___x_1613_);
                            if v___x_1615_ == 0 {
                                lean_del_object(v___x_1610_);
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
                                lean_dec_ref(v___y_1606_);
                                lean_dec(v___y_1604_);
                                lean_dec_ref(v___y_1603_);
                                lean_dec_ref(v___y_1601_);
                                lean_dec_ref(v___y_1597_);
                                v___x_1616_ = lean_box(0);
                                if v_isShared_1611_ == 0 {
                                    lean_ctor_set(v___x_1610_, 0, v___x_1616_);
                                    v___x_1618_ = v___x_1610_;
                                    state = 17;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
                                    v___x_1618_ = v_reuseFailAlloc_1619_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_1610_);
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
                        lean_del_object(v___x_1610_);
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
                    v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
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
                    if lean_obj_tag(v___x_1648_) == 0 {
                        v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
                        lean_inc(v_a_1649_);
                        lean_dec_ref_known(v___x_1648_, 1);
                        v___x_1650_ = (lean_unbox(v_a_1649_) as u8);
                        lean_dec(v_a_1649_);
                        if v___x_1650_ == 0 {
                            v___x_1651_ = lean_box(0);
                            lean_inc(v___y_1635_);
                            lean_inc_ref(v___y_1644_);
                            lean_inc(v___y_1643_);
                            lean_inc_ref(v___y_1638_);
                            lean_inc_ref(v___y_1647_);
                            lean_inc(v___y_1633_);
                            lean_inc_ref(v___y_1645_);
                            v___x_1652_ = lean_apply_9(
                                v___y_1631_,
                                v___x_1651_,
                                v___y_1645_,
                                v___y_1633_,
                                v___y_1647_,
                                v___y_1638_,
                                v___y_1643_,
                                v___y_1644_,
                                v___y_1635_,
                                lean_box(0),
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
                            v_name_1653_ = lean_ctor_get(v___y_1639_, 0);
                            v___x_1654_ =
                                l_Lean_Meta_isInstance___redArg(v_name_1653_, v___y_1635_);
                            if lean_obj_tag(v___x_1654_) == 0 {
                                v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
                                lean_inc(v_a_1655_);
                                lean_dec_ref_known(v___x_1654_, 1);
                                v___x_1656_ = (lean_unbox(v_a_1655_) as u8);
                                lean_dec(v_a_1655_);
                                if v___x_1656_ == 0 {
                                    v___x_1657_ = lean_box(0);
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
                                        lean_dec_ref(v___y_1646_);
                                        lean_dec(v___y_1642_);
                                        lean_dec_ref(v___y_1639_);
                                        lean_dec_ref(v___y_1636_);
                                        lean_dec_ref(v___y_1631_);
                                        lean_dec_ref(v___y_1630_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1661_ = lean_box(0);
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
                                lean_dec_ref(v___y_1631_);
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
                        lean_dec_ref(v___y_1631_);
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
                    lean_dec_ref(v___y_1631_);
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
                v_config_1675_ = lean_ctor_get(v___y_1668_, 1);
                v_inlineDefs_1676_ = lean_ctor_get_uint8(v_config_1675_, 3 as u32);
                if v_inlineDefs_1676_ == 0 {
                    lean_dec_ref(v_args_1666_);
                    lean_dec(v_us_1665_);
                    lean_dec(v_declName_1664_);
                    v___x_1677_ = lean_box(0);
                    v___x_1678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                    return v___x_1678_;
                } else {
                    v_inlinePartial_1679_ = lean_ctor_get_uint8(v_config_1675_, 1 as u32);
                    v___x_1680_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_1671_);
                    if lean_obj_tag(v___x_1680_) == 0 {
                        v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
                        lean_inc(v_a_1681_);
                        lean_dec_ref_known(v___x_1680_, 1);
                        v___x_1682_ = (lean_unbox(v_a_1681_) as u8);
                        v___x_1683_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                            v_declName_1664_,
                            v___x_1682_,
                            v___y_1673_,
                            v___y_1674_,
                        );
                        if lean_obj_tag(v___x_1683_) == 0 {
                            v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
                            v_isSharedCheck_1704_ = (!lean_is_exclusive(v___x_1683_)) as u8;
                            if v_isSharedCheck_1704_ == 0 {
                                v___x_1686_ = v___x_1683_;
                                v_isShared_1687_ = v_isSharedCheck_1704_;
                                state = 22;
                                continue;
                            } else {
                                lean_inc(v_a_1684_);
                                lean_dec(v___x_1683_);
                                v___x_1686_ = lean_box(0);
                                v_isShared_1687_ = v_isSharedCheck_1704_;
                                state = 22;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1681_);
                            lean_dec_ref(v_args_1666_);
                            lean_dec(v_us_1665_);
                            v_a_1705_ = lean_ctor_get(v___x_1683_, 0);
                            v_isSharedCheck_1712_ = (!lean_is_exclusive(v___x_1683_)) as u8;
                            if v_isSharedCheck_1712_ == 0 {
                                v___x_1707_ = v___x_1683_;
                                v_isShared_1708_ = v_isSharedCheck_1712_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_1705_);
                                lean_dec(v___x_1683_);
                                v___x_1707_ = lean_box(0);
                                v_isShared_1708_ = v_isSharedCheck_1712_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_args_1666_);
                        lean_dec(v_us_1665_);
                        lean_dec(v_declName_1664_);
                        v_a_1713_ = lean_ctor_get(v___x_1680_, 0);
                        v_isSharedCheck_1720_ = (!lean_is_exclusive(v___x_1680_)) as u8;
                        if v_isSharedCheck_1720_ == 0 {
                            v___x_1715_ = v___x_1680_;
                            v_isShared_1716_ = v_isSharedCheck_1720_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_1713_);
                            lean_dec(v___x_1680_);
                            v___x_1715_ = lean_box(0);
                            v_isShared_1716_ = v_isSharedCheck_1720_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            22 => {
                if lean_obj_tag(v_a_1684_) == 1 {
                    v_val_1688_ = lean_ctor_get(v_a_1684_, 0);
                    lean_inc(v_val_1688_);
                    lean_dec_ref_known(v_a_1684_, 1);
                    v___x_1689_ = (lean_unbox(v_a_1681_) as u8);
                    lean_dec(v_a_1681_);
                    v___x_1690_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_1689_);
                    if v___x_1690_ == 0 {
                        v_value_1691_ = lean_ctor_get(v_val_1688_, 1);
                        if lean_obj_tag(v_value_1691_) == 0 {
                            lean_del_object(v___x_1686_);
                            v_toSignature_1692_ = lean_ctor_get(v_val_1688_, 0);
                            lean_inc_ref(v_toSignature_1692_);
                            v_recursive_1693_ = lean_ctor_get_uint8(
                                v_val_1688_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            );
                            v_code_1694_ = lean_ctor_get(v_value_1691_, 0);
                            lean_inc_ref_n(v_code_1694_, 2);
                            v___x_1695_ =
                                l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_1688_);
                            v___x_1696_ = lean_box((v___x_1695_) as usize);
                            v___x_1697_ = lean_box((v_mustInline_1512_) as usize);
                            v___x_1698_ = lean_box((v_inlineDefs_1676_) as usize);
                            lean_inc(v_val_1688_);
                            v___f_1699_ = lean_alloc_closure(
                                l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                14,
                                5,
                            );
                            lean_closure_set(v___f_1699_, 0, v_val_1688_);
                            lean_closure_set(v___f_1699_, 1, v___x_1696_);
                            lean_closure_set(v___f_1699_, 2, v_code_1694_);
                            lean_closure_set(v___f_1699_, 3, v___x_1697_);
                            lean_closure_set(v___f_1699_, 4, v___x_1698_);
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
                                    lean_dec_ref(v___f_1699_);
                                    lean_dec_ref(v_code_1694_);
                                    lean_dec_ref(v_toSignature_1692_);
                                    lean_dec(v_val_1688_);
                                    lean_dec_ref(v_args_1666_);
                                    lean_dec(v_us_1665_);
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
                            lean_dec(v_val_1688_);
                            lean_dec_ref(v_args_1666_);
                            lean_dec(v_us_1665_);
                            v___x_1700_ = lean_box(0);
                            if v_isShared_1687_ == 0 {
                                lean_ctor_set(v___x_1686_, 0, v___x_1700_);
                                v___x_1702_ = v___x_1686_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
                                v___x_1702_ = v_reuseFailAlloc_1703_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_1688_);
                        lean_del_object(v___x_1686_);
                        lean_dec_ref(v_args_1666_);
                        lean_dec(v_us_1665_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1686_);
                    lean_dec(v_a_1684_);
                    lean_dec(v_a_1681_);
                    lean_dec_ref(v_args_1666_);
                    lean_dec(v_us_1665_);
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
                    v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
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
                    v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
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
                if lean_obj_tag(v___x_1731_) == 0 {
                    lean_dec_ref_known(v___x_1731_, 1);
                    v___x_1732_ = lean_st_ref_take(v___y_1730_);
                    v_subst_1733_ = lean_ctor_get(v___x_1732_, 0);
                    v_used_1734_ = lean_ctor_get(v___x_1732_, 1);
                    v_binderRenaming_1735_ = lean_ctor_get(v___x_1732_, 2);
                    v_funDeclInfoMap_1736_ = lean_ctor_get(v___x_1732_, 3);
                    v_simplified_1737_ = lean_ctor_get_uint8(
                        v___x_1732_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    v_visited_1738_ = lean_ctor_get(v___x_1732_, 4);
                    v_inline_1739_ = lean_ctor_get(v___x_1732_, 5);
                    v_inlineLocal_1740_ = lean_ctor_get(v___x_1732_, 6);
                    v_isSharedCheck_1771_ = (!lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1771_ == 0 {
                        v___x_1742_ = v___x_1732_;
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_inlineLocal_1740_);
                        lean_inc(v_inline_1739_);
                        lean_inc(v_visited_1738_);
                        lean_inc(v_funDeclInfoMap_1736_);
                        lean_inc(v_binderRenaming_1735_);
                        lean_inc(v_used_1734_);
                        lean_inc(v_subst_1733_);
                        lean_dec(v___x_1732_);
                        v___x_1742_ = lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1771_;
                        state = 29;
                        continue;
                    }
                } else {
                    lean_dec(v___y_1727_);
                    lean_dec_ref(v___y_1724_);
                    lean_dec_ref(v___y_1722_);
                    v_a_1772_ = lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1779_ = (!lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1779_ == 0 {
                        v___x_1774_ = v___x_1731_;
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_1772_);
                        lean_dec(v___x_1731_);
                        v___x_1774_ = lean_box(0);
                        v_isShared_1775_ = v_isSharedCheck_1779_;
                        state = 35;
                        continue;
                    }
                }
            }
            29 => {
                v___x_1744_ = lean_unsigned_to_nat(1);
                v___x_1745_ = lean_nat_add(v_inlineLocal_1740_, v___x_1744_);
                lean_dec(v_inlineLocal_1740_);
                if v_isShared_1743_ == 0 {
                    lean_ctor_set(v___x_1742_, 6, v___x_1745_);
                    v___x_1747_ = v___x_1742_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_subst_1733_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_used_1734_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_binderRenaming_1735_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_funDeclInfoMap_1736_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_visited_1738_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 5, v_inline_1739_);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 6, v___x_1745_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1770_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
                if lean_obj_tag(v___x_1749_) == 0 {
                    v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
                    v_isSharedCheck_1761_ = (!lean_is_exclusive(v___x_1749_)) as u8;
                    if v_isSharedCheck_1761_ == 0 {
                        v___x_1752_ = v___x_1749_;
                        v_isShared_1753_ = v_isSharedCheck_1761_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_1750_);
                        lean_dec(v___x_1749_);
                        v___x_1752_ = lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1761_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_1724_);
                    lean_dec_ref(v___y_1722_);
                    v_a_1762_ = lean_ctor_get(v___x_1749_, 0);
                    v_isSharedCheck_1769_ = (!lean_is_exclusive(v___x_1749_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1749_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_1762_);
                        lean_dec(v___x_1749_);
                        v___x_1764_ = lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 33;
                        continue;
                    }
                }
            }
            31 => {
                v_params_1754_ = lean_ctor_get(v___y_1724_, 2);
                lean_inc_ref(v_params_1754_);
                v_value_1755_ = lean_ctor_get(v___y_1724_, 4);
                lean_inc_ref(v_value_1755_);
                lean_dec_ref(v___y_1724_);
                v___x_1756_ = lean_alloc_ctor(0, 4, (3) as u32);
                lean_ctor_set(v___x_1756_, 0, v_params_1754_);
                lean_ctor_set(v___x_1756_, 1, v_value_1755_);
                lean_ctor_set(v___x_1756_, 2, v_a_1750_);
                lean_ctor_set(v___x_1756_, 3, v___y_1722_);
                lean_ctor_set_uint8(
                    v___x_1756_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_1729_,
                );
                lean_ctor_set_uint8(
                    v___x_1756_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    v_mustInline_1512_,
                );
                lean_ctor_set_uint8(
                    v___x_1756_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 2) as u32,
                    v_mustInline_1512_,
                );
                v___x_1757_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1757_, 0, v___x_1756_);
                if v_isShared_1753_ == 0 {
                    lean_ctor_set(v___x_1752_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1752_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
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
                    v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
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
                    v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
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
                if lean_obj_tag(v___x_1790_) == 0 {
                    v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v___x_1790_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1793_ = v___x_1790_;
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_a_1791_);
                        lean_dec(v___x_1790_);
                        v___x_1793_ = lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1801_;
                        state = 38;
                        continue;
                    }
                } else {
                    lean_dec(v___y_1784_);
                    lean_dec_ref(v___y_1783_);
                    lean_dec_ref(v___y_1781_);
                    v_a_1802_ = lean_ctor_get(v___x_1790_, 0);
                    v_isSharedCheck_1809_ = (!lean_is_exclusive(v___x_1790_)) as u8;
                    if v_isSharedCheck_1809_ == 0 {
                        v___x_1804_ = v___x_1790_;
                        v_isShared_1805_ = v_isSharedCheck_1809_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_1802_);
                        lean_dec(v___x_1790_);
                        v___x_1804_ = lean_box(0);
                        v_isShared_1805_ = v_isSharedCheck_1809_;
                        state = 40;
                        continue;
                    }
                }
            }
            38 => {
                v___x_1795_ = 1;
                if v___y_1787_ == 0 {
                    v___x_1796_ = (lean_unbox(v_a_1791_) as u8);
                    lean_dec(v_a_1791_);
                    if v___x_1796_ == 0 {
                        lean_dec(v___y_1784_);
                        lean_dec_ref(v___y_1783_);
                        lean_dec_ref(v___y_1781_);
                        v___x_1797_ = lean_box(0);
                        if v_isShared_1794_ == 0 {
                            lean_ctor_set(v___x_1793_, 0, v___x_1797_);
                            v___x_1799_ = v___x_1793_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
                            v___x_1799_ = v_reuseFailAlloc_1800_;
                            state = 39;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1793_);
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
                    lean_del_object(v___x_1793_);
                    lean_dec(v_a_1791_);
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
                    v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
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
                lean_inc(v_fvarId_1811_);
                v___x_1820_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(
                    v___x_1819_,
                    v_fvarId_1811_,
                    v___y_1816_,
                );
                if lean_obj_tag(v___x_1820_) == 0 {
                    v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
                    v_isSharedCheck_1838_ = (!lean_is_exclusive(v___x_1820_)) as u8;
                    if v_isSharedCheck_1838_ == 0 {
                        v___x_1823_ = v___x_1820_;
                        v_isShared_1824_ = v_isSharedCheck_1838_;
                        state = 43;
                        continue;
                    } else {
                        lean_inc(v_a_1821_);
                        lean_dec(v___x_1820_);
                        v___x_1823_ = lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1838_;
                        state = 43;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_1812_);
                    lean_dec(v_fvarId_1811_);
                    v_a_1839_ = lean_ctor_get(v___x_1820_, 0);
                    v_isSharedCheck_1846_ = (!lean_is_exclusive(v___x_1820_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v___x_1841_ = v___x_1820_;
                        v_isShared_1842_ = v_isSharedCheck_1846_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_1839_);
                        lean_dec(v___x_1820_);
                        v___x_1841_ = lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1846_;
                        state = 46;
                        continue;
                    }
                }
            }
            43 => {
                if lean_obj_tag(v_a_1821_) == 1 {
                    if v_mustInline_1813_ == 0 {
                        v_val_1825_ = lean_ctor_get(v_a_1821_, 0);
                        lean_inc(v_val_1825_);
                        lean_dec_ref_known(v_a_1821_, 1);
                        v___x_1826_ = lean_unsigned_to_nat(0);
                        v___x_1827_ = lean_array_get_size(v_args_1812_);
                        v___x_1828_ = lean_nat_dec_lt(v___x_1826_, v___x_1827_);
                        if v___x_1828_ == 0 {
                            lean_dec(v_val_1825_);
                            lean_dec_ref(v_args_1812_);
                            lean_dec(v_fvarId_1811_);
                            v___x_1829_ = lean_box(0);
                            if v_isShared_1824_ == 0 {
                                lean_ctor_set(v___x_1823_, 0, v___x_1829_);
                                v___x_1831_ = v___x_1823_;
                                state = 44;
                                continue;
                            } else {
                                v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                                v___x_1831_ = v_reuseFailAlloc_1832_;
                                state = 44;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1823_);
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
                        lean_del_object(v___x_1823_);
                        v_val_1833_ = lean_ctor_get(v_a_1821_, 0);
                        lean_inc(v_val_1833_);
                        lean_dec_ref_known(v_a_1821_, 1);
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
                    lean_dec(v_a_1821_);
                    lean_dec_ref(v_args_1812_);
                    lean_dec(v_fvarId_1811_);
                    v___x_1834_ = lean_box(0);
                    if v_isShared_1824_ == 0 {
                        lean_ctor_set(v___x_1823_, 0, v___x_1834_);
                        v___x_1836_ = v___x_1823_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
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
                    v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1844_;
            }
            48 => {
                if lean_obj_tag(v_e_1848_) == 3 {
                    v_declName_1857_ = lean_ctor_get(v_e_1848_, 0);
                    lean_inc(v_declName_1857_);
                    v_us_1858_ = lean_ctor_get(v_e_1848_, 1);
                    lean_inc(v_us_1858_);
                    v_args_1859_ = lean_ctor_get(v_e_1848_, 2);
                    lean_inc_ref(v_args_1859_);
                    lean_dec_ref_known(v_e_1848_, 3);
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
                    if lean_obj_tag(v_e_1848_) == 4 {
                        v_fvarId_1860_ = lean_ctor_get(v_e_1848_, 0);
                        lean_inc(v_fvarId_1860_);
                        v_args_1861_ = lean_ctor_get(v_e_1848_, 1);
                        lean_inc_ref(v_args_1861_);
                        lean_dec_ref_known(v_e_1848_, 2);
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
                        lean_dec(v_e_1848_);
                        v___x_1862_ = lean_box(0);
                        v___x_1863_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1863_, 0, v___x_1862_);
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
                    v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
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
                    v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
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
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
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
                    v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
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
                    v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
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
                    v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
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
                    v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
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
                    v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
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
    mut v_e_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
    mut v_a_1993_: *mut LeanObject,
    mut v_a_1994_: *mut LeanObject,
    mut v_a_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
    mut v_a_1997_: *mut LeanObject,
    mut v_a_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2000_: *mut LeanObject = core::ptr::null_mut();
    v_res_2000_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(
        v_e_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_,
    );
    lean_dec(v_a_1998_);
    lean_dec_ref(v_a_1997_);
    lean_dec(v_a_1996_);
    lean_dec_ref(v_a_1995_);
    lean_dec_ref(v_a_1994_);
    lean_dec(v_a_1993_);
    lean_dec_ref(v_a_1992_);
    return v_res_2000_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    v___x_2083_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_;
    v___x_2084_ = 0;
    v___x_2085_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn___closed__33_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_;
    v___x_2086_ = l_Lean_registerTraceClass(v___x_2083_, v___x_2084_, v___x_2085_);
    return v___x_2086_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2____boxed(
    mut v_a_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2088_: *mut LeanObject = core::ptr::null_mut();
    v_res_2088_ = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
    return v_res_2088_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Simp_InlineCandidate_0__Lean_Compiler_LCNF_Simp_initFn_00___x40_Lean_Compiler_LCNF_Simp_InlineCandidate_1449551352____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
}
