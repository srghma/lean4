// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpM
// Imports: Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.Renaming Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Simp.JpCases Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.Config
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_maxRecDepthErrorMessage, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::Compiler::ImplementedByAttr::{
    initialize_Lean_Compiler_ImplementedByAttr, runtime_initialize_Lean_Compiler_ImplementedByAttr,
};
use crate::r#gen::Lean::Compiler::LCNF::AlphaEqv::{
    initialize_Lean_Compiler_LCNF_AlphaEqv, runtime_initialize_Lean_Compiler_LCNF_AlphaEqv,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Code_sizeLe, l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l_Lean_Compiler_LCNF_eraseFunDecl___redArg, l_Lean_Compiler_LCNF_eraseLetDecl___redArg,
    l_Lean_Compiler_LCNF_getBinderName, l_Lean_Compiler_LCNF_getConfig___redArg,
    l_Lean_Compiler_LCNF_getPhase___redArg, l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::ElimDead::{
    initialize_Lean_Compiler_LCNF_ElimDead, runtime_initialize_Lean_Compiler_LCNF_ElimDead,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::l_Lean_Compiler_LCNF_Code_internalize;
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::l_Lean_Compiler_LCNF_getDeclAt_x3f;
use crate::r#gen::Lean::Compiler::LCNF::PrettyPrinter::{
    initialize_Lean_Compiler_LCNF_PrettyPrinter,
    runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter,
};
use crate::r#gen::Lean::Compiler::LCNF::Renaming::{
    initialize_Lean_Compiler_LCNF_Renaming, runtime_initialize_Lean_Compiler_LCNF_Renaming,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Config::{
    initialize_Lean_Compiler_LCNF_Simp_Config, runtime_initialize_Lean_Compiler_LCNF_Simp_Config,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::FunDeclInfo::{
    initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo, l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add,
    l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo,
    l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline,
    l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore,
    l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update,
    runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::JpCases::{
    initialize_Lean_Compiler_LCNF_Simp_JpCases, runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isInternal;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_uint64_of_nat,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5_value:
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
    m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6_value:
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
    m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7_value:
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
    m_fun: l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instMonadSimpM: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 117, 110, 99, 116, 105, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 108, 121, 32, 105, 110, 108, 105, 110, 101, 100, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 35, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4_value: crate::leanh::LeanStringObject<156> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 156, m_capacity: 156, m_length: 155, m_data: [44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 114, 101, 109, 111, 118, 105, 110, 103, 32, 116, 104, 101, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 105, 110, 108, 105, 110, 101, 95, 105, 102, 95, 114, 101, 100, 117, 99, 101, 93, 96, 32, 102, 114, 111, 109, 32, 116, 104, 105, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 114, 32, 105, 110, 99, 114, 101, 97, 115, 105, 110, 103, 32, 116, 104, 101, 32, 108, 105, 109, 105, 116, 32, 117, 115, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 99, 111, 109, 112, 105, 108, 101, 114, 46, 109, 97, 120, 82, 101, 99, 73, 110, 108, 105, 110, 101, 73, 102, 82, 101, 100, 117, 99, 101, 32, 60, 110, 117, 109, 62, 96, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__6_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__7_value) as *mut crate::leanh::LeanObject,11260351269579028997 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__8_value) as *mut crate::leanh::LeanObject,7114391375504651962 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__10_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0_value:
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1_value:
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [46, 46, 46, 10, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2_value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 114, 101, 97, 99, 104, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 111, 114, 10, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 110, 108, 105, 110, 101, 32, 115, 116, 97, 99, 107, 58, 10, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(
    mut v_00_u03b1_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2217_, 0, v___y_2208_);
    return v___x_2217_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(
    mut v_00_u03b1_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
    mut v___y_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0(
        v_00_u03b1_2218_,
        v___y_2219_,
        v___y_2220_,
        v___y_2221_,
        v___y_2222_,
        v___y_2223_,
        v___y_2224_,
        v___y_2225_,
        v___y_2226_,
    );
    crate::leanh::lean_dec(v___y_2226_);
    crate::leanh::lean_dec_ref(v___y_2225_);
    crate::leanh::lean_dec(v___y_2224_);
    crate::leanh::lean_dec_ref(v___y_2223_);
    crate::leanh::lean_dec_ref(v___y_2222_);
    crate::leanh::lean_dec(v___y_2221_);
    crate::leanh::lean_dec_ref(v___y_2220_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(
    mut v_00_u03b1_2229_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2230_: *mut crate::leanh::LeanObject,
    mut v___y_2231_: *mut crate::leanh::LeanObject,
    mut v___y_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2247_: u8 = 0;
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2239_);
                crate::leanh::lean_inc_ref(v___y_2238_);
                crate::leanh::lean_inc(v___y_2237_);
                crate::leanh::lean_inc_ref(v___y_2236_);
                crate::leanh::lean_inc_ref(v___y_2235_);
                crate::leanh::lean_inc(v___y_2234_);
                crate::leanh::lean_inc_ref(v___y_2233_);
                v___x_2241_ = crate::leanh::lean_apply_8(
                    v___y_2231_,
                    v___y_2233_,
                    v___y_2234_,
                    v___y_2235_,
                    v___y_2236_,
                    v___y_2237_,
                    v___y_2238_,
                    v___y_2239_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2241_) == 0 {
                    v_a_2242_ = crate::leanh::lean_ctor_get(v___x_2241_, 0);
                    crate::leanh::lean_inc(v_a_2242_);
                    crate::leanh::lean_dec_ref_known(v___x_2241_, 1);
                    crate::leanh::lean_inc(v___y_2239_);
                    crate::leanh::lean_inc_ref(v___y_2238_);
                    crate::leanh::lean_inc(v___y_2237_);
                    crate::leanh::lean_inc_ref(v___y_2236_);
                    crate::leanh::lean_inc_ref(v___y_2235_);
                    crate::leanh::lean_inc(v___y_2234_);
                    crate::leanh::lean_inc_ref(v___y_2233_);
                    v___x_2243_ = crate::leanh::lean_apply_9(
                        v___y_2232_,
                        v_a_2242_,
                        v___y_2233_,
                        v___y_2234_,
                        v___y_2235_,
                        v___y_2236_,
                        v___y_2237_,
                        v___y_2238_,
                        v___y_2239_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2243_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2232_);
                    v_a_2244_ = crate::leanh::lean_ctor_get(v___x_2241_, 0);
                    v_isSharedCheck_2251_ = (!crate::leanh::lean_is_exclusive(v___x_2241_)) as u8;
                    if v_isSharedCheck_2251_ == 0 {
                        v___x_2246_ = v___x_2241_;
                        v_isShared_2247_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2244_);
                        crate::leanh::lean_dec(v___x_2241_);
                        v___x_2246_ = crate::leanh::lean_box(0);
                        v_isShared_2247_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2247_ == 0 {
                    v___x_2249_ = v___x_2246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
                    v___x_2249_ = v_reuseFailAlloc_2250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(
    mut v_00_u03b1_2252_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1(
        v_00_u03b1_2252_,
        v_00_u03b2_2253_,
        v___y_2254_,
        v___y_2255_,
        v___y_2256_,
        v___y_2257_,
        v___y_2258_,
        v___y_2259_,
        v___y_2260_,
        v___y_2261_,
        v___y_2262_,
    );
    crate::leanh::lean_dec(v___y_2262_);
    crate::leanh::lean_dec_ref(v___y_2261_);
    crate::leanh::lean_dec(v___y_2260_);
    crate::leanh::lean_dec_ref(v___y_2259_);
    crate::leanh::lean_dec_ref(v___y_2258_);
    crate::leanh::lean_dec(v___y_2257_);
    crate::leanh::lean_dec_ref(v___y_2256_);
    return v_res_2264_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2265_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2265_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__0,
    );
    v___x_2267_ = l_StateRefT_x27_instMonad___redArg(v___x_2266_);
    return v___x_2267_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM() -> *mut crate::leanh::LeanObject {
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v_toFunctor_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___f_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2319_: u8 = 0;
    let mut v_toFunctor_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___f_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_unused_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_unused_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2347_: u8 = 0;
    let mut v_unused_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v_unused_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2274_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__1,
                );
                v_toApplicative_2275_ = crate::leanh::lean_ctor_get(v___x_2274_, 0);
                v_toFunctor_2276_ = crate::leanh::lean_ctor_get(v_toApplicative_2275_, 0);
                v_toSeq_2277_ = crate::leanh::lean_ctor_get(v_toApplicative_2275_, 2);
                v_toSeqLeft_2278_ = crate::leanh::lean_ctor_get(v_toApplicative_2275_, 3);
                v_toSeqRight_2279_ = crate::leanh::lean_ctor_get(v_toApplicative_2275_, 4);
                v___f_2280_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__2;
                v___f_2281_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2276_, 2);
                v___f_2282_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2282_, 0, v_toFunctor_2276_);
                v___f_2283_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2283_, 0, v_toFunctor_2276_);
                v___x_2284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2284_, 0, v___f_2282_);
                crate::leanh::lean_ctor_set(v___x_2284_, 1, v___f_2283_);
                crate::leanh::lean_inc(v_toSeqRight_2279_);
                v___f_2285_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2285_, 0, v_toSeqRight_2279_);
                crate::leanh::lean_inc(v_toSeqLeft_2278_);
                v___f_2286_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2286_, 0, v_toSeqLeft_2278_);
                crate::leanh::lean_inc(v_toSeq_2277_);
                v___f_2287_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2287_, 0, v_toSeq_2277_);
                v___x_2288_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2284_);
                crate::leanh::lean_ctor_set(v___x_2288_, 1, v___f_2280_);
                crate::leanh::lean_ctor_set(v___x_2288_, 2, v___f_2287_);
                crate::leanh::lean_ctor_set(v___x_2288_, 3, v___f_2286_);
                crate::leanh::lean_ctor_set(v___x_2288_, 4, v___f_2285_);
                v___x_2289_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2288_);
                crate::leanh::lean_ctor_set(v___x_2289_, 1, v___f_2281_);
                v___x_2290_ = l_StateRefT_x27_instMonad___redArg(v___x_2289_);
                v_toApplicative_2291_ = crate::leanh::lean_ctor_get(v___x_2290_, 0);
                v_isSharedCheck_2349_ = (!crate::leanh::lean_is_exclusive(v___x_2290_)) as u8;
                if v_isSharedCheck_2349_ == 0 {
                    v_unused_2350_ = crate::leanh::lean_ctor_get(v___x_2290_, 1);
                    crate::leanh::lean_dec(v_unused_2350_);
                    v___x_2293_ = v___x_2290_;
                    v_isShared_2294_ = v_isSharedCheck_2349_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2291_);
                    crate::leanh::lean_dec(v___x_2290_);
                    v___x_2293_ = crate::leanh::lean_box(0);
                    v_isShared_2294_ = v_isSharedCheck_2349_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2295_ = crate::leanh::lean_ctor_get(v_toApplicative_2291_, 0);
                v_toSeq_2296_ = crate::leanh::lean_ctor_get(v_toApplicative_2291_, 2);
                v_toSeqLeft_2297_ = crate::leanh::lean_ctor_get(v_toApplicative_2291_, 3);
                v_toSeqRight_2298_ = crate::leanh::lean_ctor_get(v_toApplicative_2291_, 4);
                v_isSharedCheck_2347_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2291_)) as u8;
                if v_isSharedCheck_2347_ == 0 {
                    v_unused_2348_ = crate::leanh::lean_ctor_get(v_toApplicative_2291_, 1);
                    crate::leanh::lean_dec(v_unused_2348_);
                    v___x_2300_ = v_toApplicative_2291_;
                    v_isShared_2301_ = v_isSharedCheck_2347_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2298_);
                    crate::leanh::lean_inc(v_toSeqLeft_2297_);
                    crate::leanh::lean_inc(v_toSeq_2296_);
                    crate::leanh::lean_inc(v_toFunctor_2295_);
                    crate::leanh::lean_dec(v_toApplicative_2291_);
                    v___x_2300_ = crate::leanh::lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2302_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__4;
                v___f_2303_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_2295_);
                v___f_2304_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2304_, 0, v_toFunctor_2295_);
                v___f_2305_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2305_, 0, v_toFunctor_2295_);
                v___x_2306_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2306_, 0, v___f_2304_);
                crate::leanh::lean_ctor_set(v___x_2306_, 1, v___f_2305_);
                v___f_2307_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2307_, 0, v_toSeqRight_2298_);
                v___f_2308_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2308_, 0, v_toSeqLeft_2297_);
                v___f_2309_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2309_, 0, v_toSeq_2296_);
                if v_isShared_2301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2300_, 4, v___f_2307_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 3, v___f_2308_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 2, v___f_2309_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 1, v___f_2302_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2306_);
                    v___x_2311_ = v___x_2300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2346_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___f_2302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 2, v___f_2309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 3, v___f_2308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2346_, 4, v___f_2307_);
                    v___x_2311_ = v_reuseFailAlloc_2346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2293_, 1, v___f_2303_);
                    crate::leanh::lean_ctor_set(v___x_2293_, 0, v___x_2311_);
                    v___x_2313_ = v___x_2293_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___f_2303_);
                    v___x_2313_ = v_reuseFailAlloc_2345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2314_ = l_ReaderT_instMonad___redArg(v___x_2313_);
                v___x_2315_ = l_StateRefT_x27_instMonad___redArg(v___x_2314_);
                v_toApplicative_2316_ = crate::leanh::lean_ctor_get(v___x_2315_, 0);
                v_isSharedCheck_2343_ = (!crate::leanh::lean_is_exclusive(v___x_2315_)) as u8;
                if v_isSharedCheck_2343_ == 0 {
                    v_unused_2344_ = crate::leanh::lean_ctor_get(v___x_2315_, 1);
                    crate::leanh::lean_dec(v_unused_2344_);
                    v___x_2318_ = v___x_2315_;
                    v_isShared_2319_ = v_isSharedCheck_2343_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2316_);
                    crate::leanh::lean_dec(v___x_2315_);
                    v___x_2318_ = crate::leanh::lean_box(0);
                    v_isShared_2319_ = v_isSharedCheck_2343_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2320_ = crate::leanh::lean_ctor_get(v_toApplicative_2316_, 0);
                v_toSeq_2321_ = crate::leanh::lean_ctor_get(v_toApplicative_2316_, 2);
                v_toSeqLeft_2322_ = crate::leanh::lean_ctor_get(v_toApplicative_2316_, 3);
                v_toSeqRight_2323_ = crate::leanh::lean_ctor_get(v_toApplicative_2316_, 4);
                v_isSharedCheck_2341_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2316_)) as u8;
                if v_isSharedCheck_2341_ == 0 {
                    v_unused_2342_ = crate::leanh::lean_ctor_get(v_toApplicative_2316_, 1);
                    crate::leanh::lean_dec(v_unused_2342_);
                    v___x_2325_ = v_toApplicative_2316_;
                    v_isShared_2326_ = v_isSharedCheck_2341_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2323_);
                    crate::leanh::lean_inc(v_toSeqLeft_2322_);
                    crate::leanh::lean_inc(v_toSeq_2321_);
                    crate::leanh::lean_inc(v_toFunctor_2320_);
                    crate::leanh::lean_dec(v_toApplicative_2316_);
                    v___x_2325_ = crate::leanh::lean_box(0);
                    v_isShared_2326_ = v_isSharedCheck_2341_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2327_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__6;
                v___f_2328_ = l_Lean_Compiler_LCNF_Simp_instMonadSimpM___closed__7;
                crate::leanh::lean_inc_ref(v_toFunctor_2320_);
                v___f_2329_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2329_, 0, v_toFunctor_2320_);
                v___f_2330_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2330_, 0, v_toFunctor_2320_);
                v___x_2331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2331_, 0, v___f_2329_);
                crate::leanh::lean_ctor_set(v___x_2331_, 1, v___f_2330_);
                v___f_2332_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2332_, 0, v_toSeqRight_2323_);
                v___f_2333_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2333_, 0, v_toSeqLeft_2322_);
                v___f_2334_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2334_, 0, v_toSeq_2321_);
                if v_isShared_2326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2325_, 4, v___f_2332_);
                    crate::leanh::lean_ctor_set(v___x_2325_, 3, v___f_2333_);
                    crate::leanh::lean_ctor_set(v___x_2325_, 2, v___f_2334_);
                    crate::leanh::lean_ctor_set(v___x_2325_, 1, v___f_2327_);
                    crate::leanh::lean_ctor_set(v___x_2325_, 0, v___x_2331_);
                    v___x_2336_ = v___x_2325_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___f_2327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 2, v___f_2334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 3, v___f_2333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 4, v___f_2332_);
                    v___x_2336_ = v_reuseFailAlloc_2340_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2319_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2318_, 1, v___f_2328_);
                    crate::leanh::lean_ctor_set(v___x_2318_, 0, v___x_2336_);
                    v___x_2338_ = v___x_2318_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___f_2328_);
                    v___x_2338_ = v_reuseFailAlloc_2339_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2359_ = lean_st_ref_get(v___y_2352_);
    v_subst_2360_ = crate::leanh::lean_ctor_get(v___x_2359_, 0);
    crate::leanh::lean_inc_ref(v_subst_2360_);
    crate::leanh::lean_dec(v___x_2359_);
    v___x_2361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2361_, 0, v_subst_2360_);
    return v___x_2361_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0___boxed(
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2370_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstSimpMPureFalse___lam__0(
        v___y_2362_,
        v___y_2363_,
        v___y_2364_,
        v___y_2365_,
        v___y_2366_,
        v___y_2367_,
        v___y_2368_,
    );
    crate::leanh::lean_dec(v___y_2368_);
    crate::leanh::lean_dec_ref(v___y_2367_);
    crate::leanh::lean_dec(v___y_2366_);
    crate::leanh::lean_dec_ref(v___y_2365_);
    crate::leanh::lean_dec_ref(v___y_2364_);
    crate::leanh::lean_dec(v___y_2363_);
    crate::leanh::lean_dec_ref(v___y_2362_);
    return v_res_2370_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(
    mut v_f_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2387_: u8 = 0;
    let mut v_visited_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2382_ = lean_st_ref_take(v___y_2375_);
                v_subst_2383_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                v_used_2384_ = crate::leanh::lean_ctor_get(v___x_2382_, 1);
                v_binderRenaming_2385_ = crate::leanh::lean_ctor_get(v___x_2382_, 2);
                v_funDeclInfoMap_2386_ = crate::leanh::lean_ctor_get(v___x_2382_, 3);
                v_simplified_2387_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2382_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2388_ = crate::leanh::lean_ctor_get(v___x_2382_, 4);
                v_inline_2389_ = crate::leanh::lean_ctor_get(v___x_2382_, 5);
                v_inlineLocal_2390_ = crate::leanh::lean_ctor_get(v___x_2382_, 6);
                v_isSharedCheck_2401_ = (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                if v_isSharedCheck_2401_ == 0 {
                    v___x_2392_ = v___x_2382_;
                    v_isShared_2393_ = v_isSharedCheck_2401_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2390_);
                    crate::leanh::lean_inc(v_inline_2389_);
                    crate::leanh::lean_inc(v_visited_2388_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2386_);
                    crate::leanh::lean_inc(v_binderRenaming_2385_);
                    crate::leanh::lean_inc(v_used_2384_);
                    crate::leanh::lean_inc(v_subst_2383_);
                    crate::leanh::lean_dec(v___x_2382_);
                    v___x_2392_ = crate::leanh::lean_box(0);
                    v_isShared_2393_ = v_isSharedCheck_2401_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2394_ = crate::leanh::lean_apply_1(v_f_2373_, v_subst_2383_);
                if v_isShared_2393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2392_, 0, v___x_2394_);
                    v___x_2396_ = v___x_2392_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_used_2384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_binderRenaming_2385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_funDeclInfoMap_2386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_visited_2388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 5, v_inline_2389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 6, v_inlineLocal_2390_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2400_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2387_,
                    );
                    v___x_2396_ = v_reuseFailAlloc_2400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2397_ = lean_st_ref_set(v___y_2375_, v___x_2396_);
                v___x_2398_ = crate::leanh::lean_box(0);
                v___x_2399_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2399_, 0, v___x_2398_);
                return v___x_2399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0___boxed(
    mut v_f_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_Compiler_LCNF_Simp_instMonadFVarSubstStateSimpMPure___lam__0(
        v_f_2402_,
        v___y_2403_,
        v___y_2404_,
        v___y_2405_,
        v___y_2406_,
        v___y_2407_,
        v___y_2408_,
        v___y_2409_,
    );
    crate::leanh::lean_dec(v___y_2409_);
    crate::leanh::lean_dec_ref(v___y_2408_);
    crate::leanh::lean_dec(v___y_2407_);
    crate::leanh::lean_dec_ref(v___y_2406_);
    crate::leanh::lean_dec_ref(v___y_2405_);
    crate::leanh::lean_dec(v___y_2404_);
    crate::leanh::lean_dec_ref(v___y_2403_);
    return v_res_2411_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(
    mut v_a_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2427_: u8 = 0;
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2416_ = lean_st_ref_take(v_a_2414_);
                v_subst_2417_ = crate::leanh::lean_ctor_get(v___x_2416_, 0);
                v_used_2418_ = crate::leanh::lean_ctor_get(v___x_2416_, 1);
                v_binderRenaming_2419_ = crate::leanh::lean_ctor_get(v___x_2416_, 2);
                v_funDeclInfoMap_2420_ = crate::leanh::lean_ctor_get(v___x_2416_, 3);
                v_visited_2421_ = crate::leanh::lean_ctor_get(v___x_2416_, 4);
                v_inline_2422_ = crate::leanh::lean_ctor_get(v___x_2416_, 5);
                v_inlineLocal_2423_ = crate::leanh::lean_ctor_get(v___x_2416_, 6);
                v_isSharedCheck_2434_ = (!crate::leanh::lean_is_exclusive(v___x_2416_)) as u8;
                if v_isSharedCheck_2434_ == 0 {
                    v___x_2425_ = v___x_2416_;
                    v_isShared_2426_ = v_isSharedCheck_2434_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2423_);
                    crate::leanh::lean_inc(v_inline_2422_);
                    crate::leanh::lean_inc(v_visited_2421_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2420_);
                    crate::leanh::lean_inc(v_binderRenaming_2419_);
                    crate::leanh::lean_inc(v_used_2418_);
                    crate::leanh::lean_inc(v_subst_2417_);
                    crate::leanh::lean_dec(v___x_2416_);
                    v___x_2425_ = crate::leanh::lean_box(0);
                    v_isShared_2426_ = v_isSharedCheck_2434_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2427_ = 1;
                if v_isShared_2426_ == 0 {
                    v___x_2429_ = v___x_2425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2433_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_subst_2417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_used_2418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_binderRenaming_2419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_funDeclInfoMap_2420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 4, v_visited_2421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 5, v_inline_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 6, v_inlineLocal_2423_);
                    v___x_2429_ = v_reuseFailAlloc_2433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2429_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_2427_,
                );
                v___x_2430_ = lean_st_ref_set(v_a_2414_, v___x_2429_);
                v___x_2431_ = crate::leanh::lean_box(0);
                v___x_2432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2432_, 0, v___x_2431_);
                return v___x_2432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markSimplified___redArg___boxed(
    mut v_a_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2435_);
    crate::leanh::lean_dec(v_a_2435_);
    return v_res_2437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markSimplified(
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_2439_);
    return v___x_2446_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markSimplified___boxed(
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_a_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Lean_Compiler_LCNF_Simp_markSimplified(
        v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_,
    );
    crate::leanh::lean_dec(v_a_2453_);
    crate::leanh::lean_dec_ref(v_a_2452_);
    crate::leanh::lean_dec(v_a_2451_);
    crate::leanh::lean_dec_ref(v_a_2450_);
    crate::leanh::lean_dec_ref(v_a_2449_);
    crate::leanh::lean_dec(v_a_2448_);
    crate::leanh::lean_dec_ref(v_a_2447_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incVisited___redArg(
    mut v_a_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2463_: u8 = 0;
    let mut v_visited_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2458_ = lean_st_ref_take(v_a_2456_);
                v_subst_2459_ = crate::leanh::lean_ctor_get(v___x_2458_, 0);
                v_used_2460_ = crate::leanh::lean_ctor_get(v___x_2458_, 1);
                v_binderRenaming_2461_ = crate::leanh::lean_ctor_get(v___x_2458_, 2);
                v_funDeclInfoMap_2462_ = crate::leanh::lean_ctor_get(v___x_2458_, 3);
                v_simplified_2463_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2464_ = crate::leanh::lean_ctor_get(v___x_2458_, 4);
                v_inline_2465_ = crate::leanh::lean_ctor_get(v___x_2458_, 5);
                v_inlineLocal_2466_ = crate::leanh::lean_ctor_get(v___x_2458_, 6);
                v_isSharedCheck_2478_ = (!crate::leanh::lean_is_exclusive(v___x_2458_)) as u8;
                if v_isSharedCheck_2478_ == 0 {
                    v___x_2468_ = v___x_2458_;
                    v_isShared_2469_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2466_);
                    crate::leanh::lean_inc(v_inline_2465_);
                    crate::leanh::lean_inc(v_visited_2464_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2462_);
                    crate::leanh::lean_inc(v_binderRenaming_2461_);
                    crate::leanh::lean_inc(v_used_2460_);
                    crate::leanh::lean_inc(v_subst_2459_);
                    crate::leanh::lean_dec(v___x_2458_);
                    v___x_2468_ = crate::leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2471_ = lean_nat_add(v_visited_2464_, v___x_2470_);
                crate::leanh::lean_dec(v_visited_2464_);
                if v_isShared_2469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2468_, 4, v___x_2471_);
                    v___x_2473_ = v___x_2468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_subst_2459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_used_2460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_binderRenaming_2461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_funDeclInfoMap_2462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 4, v___x_2471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 5, v_inline_2465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_inlineLocal_2466_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2477_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2463_,
                    );
                    v___x_2473_ = v_reuseFailAlloc_2477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2474_ = lean_st_ref_set(v_a_2456_, v___x_2473_);
                v___x_2475_ = crate::leanh::lean_box(0);
                v___x_2476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2476_, 0, v___x_2475_);
                return v___x_2476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incVisited___redArg___boxed(
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2479_);
    crate::leanh::lean_dec(v_a_2479_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incVisited(
    mut v_a_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
    mut v_a_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_2483_);
    return v___x_2490_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incVisited___boxed(
    mut v_a_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
    mut v_a_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2499_ = l_Lean_Compiler_LCNF_Simp_incVisited(
        v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_,
    );
    crate::leanh::lean_dec(v_a_2497_);
    crate::leanh::lean_dec_ref(v_a_2496_);
    crate::leanh::lean_dec(v_a_2495_);
    crate::leanh::lean_dec_ref(v_a_2494_);
    crate::leanh::lean_dec_ref(v_a_2493_);
    crate::leanh::lean_dec(v_a_2492_);
    crate::leanh::lean_dec_ref(v_a_2491_);
    return v_res_2499_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInline___redArg(
    mut v_a_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2507_: u8 = 0;
    let mut v_visited_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2502_ = lean_st_ref_take(v_a_2500_);
                v_subst_2503_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                v_used_2504_ = crate::leanh::lean_ctor_get(v___x_2502_, 1);
                v_binderRenaming_2505_ = crate::leanh::lean_ctor_get(v___x_2502_, 2);
                v_funDeclInfoMap_2506_ = crate::leanh::lean_ctor_get(v___x_2502_, 3);
                v_simplified_2507_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2502_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2508_ = crate::leanh::lean_ctor_get(v___x_2502_, 4);
                v_inline_2509_ = crate::leanh::lean_ctor_get(v___x_2502_, 5);
                v_inlineLocal_2510_ = crate::leanh::lean_ctor_get(v___x_2502_, 6);
                v_isSharedCheck_2522_ = (!crate::leanh::lean_is_exclusive(v___x_2502_)) as u8;
                if v_isSharedCheck_2522_ == 0 {
                    v___x_2512_ = v___x_2502_;
                    v_isShared_2513_ = v_isSharedCheck_2522_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2510_);
                    crate::leanh::lean_inc(v_inline_2509_);
                    crate::leanh::lean_inc(v_visited_2508_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2506_);
                    crate::leanh::lean_inc(v_binderRenaming_2505_);
                    crate::leanh::lean_inc(v_used_2504_);
                    crate::leanh::lean_inc(v_subst_2503_);
                    crate::leanh::lean_dec(v___x_2502_);
                    v___x_2512_ = crate::leanh::lean_box(0);
                    v_isShared_2513_ = v_isSharedCheck_2522_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2514_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2515_ = lean_nat_add(v_inline_2509_, v___x_2514_);
                crate::leanh::lean_dec(v_inline_2509_);
                if v_isShared_2513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2512_, 5, v___x_2515_);
                    v___x_2517_ = v___x_2512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_subst_2503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_used_2504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_binderRenaming_2505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_funDeclInfoMap_2506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_visited_2508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 5, v___x_2515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_inlineLocal_2510_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2521_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2507_,
                    );
                    v___x_2517_ = v_reuseFailAlloc_2521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2518_ = lean_st_ref_set(v_a_2500_, v___x_2517_);
                v___x_2519_ = crate::leanh::lean_box(0);
                v___x_2520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2519_);
                return v___x_2520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInline___redArg___boxed(
    mut v_a_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_2523_);
    crate::leanh::lean_dec(v_a_2523_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInline(
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
    mut v_a_2529_: *mut crate::leanh::LeanObject,
    mut v_a_2530_: *mut crate::leanh::LeanObject,
    mut v_a_2531_: *mut crate::leanh::LeanObject,
    mut v_a_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2534_ = l_Lean_Compiler_LCNF_Simp_incInline___redArg(v_a_2527_);
    return v___x_2534_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInline___boxed(
    mut v_a_2535_: *mut crate::leanh::LeanObject,
    mut v_a_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
    mut v_a_2539_: *mut crate::leanh::LeanObject,
    mut v_a_2540_: *mut crate::leanh::LeanObject,
    mut v_a_2541_: *mut crate::leanh::LeanObject,
    mut v_a_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2543_ = l_Lean_Compiler_LCNF_Simp_incInline(
        v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_,
    );
    crate::leanh::lean_dec(v_a_2541_);
    crate::leanh::lean_dec_ref(v_a_2540_);
    crate::leanh::lean_dec(v_a_2539_);
    crate::leanh::lean_dec_ref(v_a_2538_);
    crate::leanh::lean_dec_ref(v_a_2537_);
    crate::leanh::lean_dec(v_a_2536_);
    crate::leanh::lean_dec_ref(v_a_2535_);
    return v_res_2543_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(
    mut v_a_2544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2551_: u8 = 0;
    let mut v_visited_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2546_ = lean_st_ref_take(v_a_2544_);
                v_subst_2547_ = crate::leanh::lean_ctor_get(v___x_2546_, 0);
                v_used_2548_ = crate::leanh::lean_ctor_get(v___x_2546_, 1);
                v_binderRenaming_2549_ = crate::leanh::lean_ctor_get(v___x_2546_, 2);
                v_funDeclInfoMap_2550_ = crate::leanh::lean_ctor_get(v___x_2546_, 3);
                v_simplified_2551_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2546_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2552_ = crate::leanh::lean_ctor_get(v___x_2546_, 4);
                v_inline_2553_ = crate::leanh::lean_ctor_get(v___x_2546_, 5);
                v_inlineLocal_2554_ = crate::leanh::lean_ctor_get(v___x_2546_, 6);
                v_isSharedCheck_2566_ = (!crate::leanh::lean_is_exclusive(v___x_2546_)) as u8;
                if v_isSharedCheck_2566_ == 0 {
                    v___x_2556_ = v___x_2546_;
                    v_isShared_2557_ = v_isSharedCheck_2566_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2554_);
                    crate::leanh::lean_inc(v_inline_2553_);
                    crate::leanh::lean_inc(v_visited_2552_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2550_);
                    crate::leanh::lean_inc(v_binderRenaming_2549_);
                    crate::leanh::lean_inc(v_used_2548_);
                    crate::leanh::lean_inc(v_subst_2547_);
                    crate::leanh::lean_dec(v___x_2546_);
                    v___x_2556_ = crate::leanh::lean_box(0);
                    v_isShared_2557_ = v_isSharedCheck_2566_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2558_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2559_ = lean_nat_add(v_inlineLocal_2554_, v___x_2558_);
                crate::leanh::lean_dec(v_inlineLocal_2554_);
                if v_isShared_2557_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2556_, 6, v___x_2559_);
                    v___x_2561_ = v___x_2556_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_subst_2547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_used_2548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_binderRenaming_2549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_funDeclInfoMap_2550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_visited_2552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 5, v_inline_2553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 6, v___x_2559_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2565_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2551_,
                    );
                    v___x_2561_ = v_reuseFailAlloc_2565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2562_ = lean_st_ref_set(v_a_2544_, v___x_2561_);
                v___x_2563_ = crate::leanh::lean_box(0);
                v___x_2564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
                return v___x_2564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg___boxed(
    mut v_a_2567_: *mut crate::leanh::LeanObject,
    mut v_a_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_2567_);
    crate::leanh::lean_dec(v_a_2567_);
    return v_res_2569_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInlineLocal(
    mut v_a_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
    mut v_a_2572_: *mut crate::leanh::LeanObject,
    mut v_a_2573_: *mut crate::leanh::LeanObject,
    mut v_a_2574_: *mut crate::leanh::LeanObject,
    mut v_a_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal___redArg(v_a_2571_);
    return v___x_2578_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_incInlineLocal___boxed(
    mut v_a_2579_: *mut crate::leanh::LeanObject,
    mut v_a_2580_: *mut crate::leanh::LeanObject,
    mut v_a_2581_: *mut crate::leanh::LeanObject,
    mut v_a_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lean_Compiler_LCNF_Simp_incInlineLocal(
        v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_,
    );
    crate::leanh::lean_dec(v_a_2585_);
    crate::leanh::lean_dec_ref(v_a_2584_);
    crate::leanh::lean_dec(v_a_2583_);
    crate::leanh::lean_dec_ref(v_a_2582_);
    crate::leanh::lean_dec_ref(v_a_2581_);
    crate::leanh::lean_dec(v_a_2580_);
    crate::leanh::lean_dec_ref(v_a_2579_);
    return v_res_2587_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(
    mut v_fvarId_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2596_: u8 = 0;
    let mut v_visited_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2602_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2591_ = lean_st_ref_take(v_a_2589_);
                v_subst_2592_ = crate::leanh::lean_ctor_get(v___x_2591_, 0);
                v_used_2593_ = crate::leanh::lean_ctor_get(v___x_2591_, 1);
                v_binderRenaming_2594_ = crate::leanh::lean_ctor_get(v___x_2591_, 2);
                v_funDeclInfoMap_2595_ = crate::leanh::lean_ctor_get(v___x_2591_, 3);
                v_simplified_2596_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2591_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2597_ = crate::leanh::lean_ctor_get(v___x_2591_, 4);
                v_inline_2598_ = crate::leanh::lean_ctor_get(v___x_2591_, 5);
                v_inlineLocal_2599_ = crate::leanh::lean_ctor_get(v___x_2591_, 6);
                v_isSharedCheck_2610_ = (!crate::leanh::lean_is_exclusive(v___x_2591_)) as u8;
                if v_isSharedCheck_2610_ == 0 {
                    v___x_2601_ = v___x_2591_;
                    v_isShared_2602_ = v_isSharedCheck_2610_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2599_);
                    crate::leanh::lean_inc(v_inline_2598_);
                    crate::leanh::lean_inc(v_visited_2597_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2595_);
                    crate::leanh::lean_inc(v_binderRenaming_2594_);
                    crate::leanh::lean_inc(v_used_2593_);
                    crate::leanh::lean_inc(v_subst_2592_);
                    crate::leanh::lean_dec(v___x_2591_);
                    v___x_2601_ = crate::leanh::lean_box(0);
                    v_isShared_2602_ = v_isSharedCheck_2610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2603_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(
                    v_funDeclInfoMap_2595_,
                    v_fvarId_2588_,
                );
                if v_isShared_2602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2601_, 3, v___x_2603_);
                    v___x_2605_ = v___x_2601_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_subst_2592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_used_2593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 2, v_binderRenaming_2594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 3, v___x_2603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 4, v_visited_2597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 5, v_inline_2598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 6, v_inlineLocal_2599_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2609_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2596_,
                    );
                    v___x_2605_ = v_reuseFailAlloc_2609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2606_ = lean_st_ref_set(v_a_2589_, v___x_2605_);
                v___x_2607_ = crate::leanh::lean_box(0);
                v___x_2608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2607_);
                return v___x_2608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addMustInline___redArg___boxed(
    mut v_fvarId_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2614_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_2611_, v_a_2612_);
    crate::leanh::lean_dec(v_a_2612_);
    return v_res_2614_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addMustInline(
    mut v_fvarId_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_2615_, v_a_2617_);
    return v___x_2624_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addMustInline___boxed(
    mut v_fvarId_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_a_2629_: *mut crate::leanh::LeanObject,
    mut v_a_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2634_ = l_Lean_Compiler_LCNF_Simp_addMustInline(
        v_fvarId_2625_,
        v_a_2626_,
        v_a_2627_,
        v_a_2628_,
        v_a_2629_,
        v_a_2630_,
        v_a_2631_,
        v_a_2632_,
    );
    crate::leanh::lean_dec(v_a_2632_);
    crate::leanh::lean_dec_ref(v_a_2631_);
    crate::leanh::lean_dec(v_a_2630_);
    crate::leanh::lean_dec_ref(v_a_2629_);
    crate::leanh::lean_dec_ref(v_a_2628_);
    crate::leanh::lean_dec(v_a_2627_);
    crate::leanh::lean_dec_ref(v_a_2626_);
    return v_res_2634_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(
    mut v_fvarId_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2643_: u8 = 0;
    let mut v_visited_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2638_ = lean_st_ref_take(v_a_2636_);
                v_subst_2639_ = crate::leanh::lean_ctor_get(v___x_2638_, 0);
                v_used_2640_ = crate::leanh::lean_ctor_get(v___x_2638_, 1);
                v_binderRenaming_2641_ = crate::leanh::lean_ctor_get(v___x_2638_, 2);
                v_funDeclInfoMap_2642_ = crate::leanh::lean_ctor_get(v___x_2638_, 3);
                v_simplified_2643_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2644_ = crate::leanh::lean_ctor_get(v___x_2638_, 4);
                v_inline_2645_ = crate::leanh::lean_ctor_get(v___x_2638_, 5);
                v_inlineLocal_2646_ = crate::leanh::lean_ctor_get(v___x_2638_, 6);
                v_isSharedCheck_2657_ = (!crate::leanh::lean_is_exclusive(v___x_2638_)) as u8;
                if v_isSharedCheck_2657_ == 0 {
                    v___x_2648_ = v___x_2638_;
                    v_isShared_2649_ = v_isSharedCheck_2657_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2646_);
                    crate::leanh::lean_inc(v_inline_2645_);
                    crate::leanh::lean_inc(v_visited_2644_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2642_);
                    crate::leanh::lean_inc(v_binderRenaming_2641_);
                    crate::leanh::lean_inc(v_used_2640_);
                    crate::leanh::lean_inc(v_subst_2639_);
                    crate::leanh::lean_dec(v___x_2638_);
                    v___x_2648_ = crate::leanh::lean_box(0);
                    v_isShared_2649_ = v_isSharedCheck_2657_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2650_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(
                    v_funDeclInfoMap_2642_,
                    v_fvarId_2635_,
                );
                if v_isShared_2649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2648_, 3, v___x_2650_);
                    v___x_2652_ = v___x_2648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2656_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_subst_2639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_used_2640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_binderRenaming_2641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 3, v___x_2650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_visited_2644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 5, v_inline_2645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 6, v_inlineLocal_2646_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2656_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2643_,
                    );
                    v___x_2652_ = v_reuseFailAlloc_2656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2653_ = lean_st_ref_set(v_a_2636_, v___x_2652_);
                v___x_2654_ = crate::leanh::lean_box(0);
                v___x_2655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2655_, 0, v___x_2654_);
                return v___x_2655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg___boxed(
    mut v_fvarId_2658_: *mut crate::leanh::LeanObject,
    mut v_a_2659_: *mut crate::leanh::LeanObject,
    mut v_a_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2661_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_2658_, v_a_2659_);
    crate::leanh::lean_dec(v_a_2659_);
    return v_res_2661_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunOcc(
    mut v_fvarId_2662_: *mut crate::leanh::LeanObject,
    mut v_a_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
    mut v_a_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = l_Lean_Compiler_LCNF_Simp_addFunOcc___redArg(v_fvarId_2662_, v_a_2664_);
    return v___x_2671_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunOcc___boxed(
    mut v_fvarId_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
    mut v_a_2676_: *mut crate::leanh::LeanObject,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2681_ = l_Lean_Compiler_LCNF_Simp_addFunOcc(
        v_fvarId_2672_,
        v_a_2673_,
        v_a_2674_,
        v_a_2675_,
        v_a_2676_,
        v_a_2677_,
        v_a_2678_,
        v_a_2679_,
    );
    crate::leanh::lean_dec(v_a_2679_);
    crate::leanh::lean_dec_ref(v_a_2678_);
    crate::leanh::lean_dec(v_a_2677_);
    crate::leanh::lean_dec_ref(v_a_2676_);
    crate::leanh::lean_dec_ref(v_a_2675_);
    crate::leanh::lean_dec(v_a_2674_);
    crate::leanh::lean_dec_ref(v_a_2673_);
    return v_res_2681_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(
    mut v_fvarId_2682_: *mut crate::leanh::LeanObject,
    mut v_a_2683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2690_: u8 = 0;
    let mut v_visited_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2685_ = lean_st_ref_take(v_a_2683_);
                v_subst_2686_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                v_used_2687_ = crate::leanh::lean_ctor_get(v___x_2685_, 1);
                v_binderRenaming_2688_ = crate::leanh::lean_ctor_get(v___x_2685_, 2);
                v_funDeclInfoMap_2689_ = crate::leanh::lean_ctor_get(v___x_2685_, 3);
                v_simplified_2690_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2685_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2691_ = crate::leanh::lean_ctor_get(v___x_2685_, 4);
                v_inline_2692_ = crate::leanh::lean_ctor_get(v___x_2685_, 5);
                v_inlineLocal_2693_ = crate::leanh::lean_ctor_get(v___x_2685_, 6);
                v_isSharedCheck_2704_ = (!crate::leanh::lean_is_exclusive(v___x_2685_)) as u8;
                if v_isSharedCheck_2704_ == 0 {
                    v___x_2695_ = v___x_2685_;
                    v_isShared_2696_ = v_isSharedCheck_2704_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2693_);
                    crate::leanh::lean_inc(v_inline_2692_);
                    crate::leanh::lean_inc(v_visited_2691_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2689_);
                    crate::leanh::lean_inc(v_binderRenaming_2688_);
                    crate::leanh::lean_inc(v_used_2687_);
                    crate::leanh::lean_inc(v_subst_2686_);
                    crate::leanh::lean_dec(v___x_2685_);
                    v___x_2695_ = crate::leanh::lean_box(0);
                    v_isShared_2696_ = v_isSharedCheck_2704_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2697_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(
                    v_funDeclInfoMap_2689_,
                    v_fvarId_2682_,
                );
                if v_isShared_2696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2695_, 3, v___x_2697_);
                    v___x_2699_ = v___x_2695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_subst_2686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 1, v_used_2687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 2, v_binderRenaming_2688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 3, v___x_2697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 4, v_visited_2691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 5, v_inline_2692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 6, v_inlineLocal_2693_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2703_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2690_,
                    );
                    v___x_2699_ = v_reuseFailAlloc_2703_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2700_ = lean_st_ref_set(v_a_2683_, v___x_2699_);
                v___x_2701_ = crate::leanh::lean_box(0);
                v___x_2702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                return v___x_2702_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg___boxed(
    mut v_fvarId_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_2705_, v_a_2706_);
    crate::leanh::lean_dec(v_a_2706_);
    return v_res_2708_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunHoOcc(
    mut v_fvarId_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc___redArg(v_fvarId_2709_, v_a_2711_);
    return v___x_2718_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFunHoOcc___boxed(
    mut v_fvarId_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2728_ = l_Lean_Compiler_LCNF_Simp_addFunHoOcc(
        v_fvarId_2719_,
        v_a_2720_,
        v_a_2721_,
        v_a_2722_,
        v_a_2723_,
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
    );
    crate::leanh::lean_dec(v_a_2726_);
    crate::leanh::lean_dec_ref(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    crate::leanh::lean_dec_ref(v_a_2723_);
    crate::leanh::lean_dec_ref(v_a_2722_);
    crate::leanh::lean_dec(v_a_2721_);
    crate::leanh::lean_dec_ref(v_a_2720_);
    return v_res_2728_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2729_ = crate::leanh::lean_box(0);
    v___x_2730_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2731_ = lean_mk_array(v___x_2730_, v___x_2729_);
    return v___x_2731_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2732_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__0,
    );
    v___x_2733_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2733_);
    crate::leanh::lean_ctor_set(v___x_2734_, 1, v___x_2732_);
    return v___x_2734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
    mut v_code_2735_: *mut crate::leanh::LeanObject,
    mut v_mustInline_2736_: u8,
    mut v_a_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v_a_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2748_: u8 = 0;
    let mut v_visited_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_2768_: u8 = 0;
    let mut v_visited_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2774_: u8 = 0;
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_unused_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut v_a_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2793_: u8 = 0;
    let mut v_reuseFailAlloc_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2743_ = lean_st_ref_take(v_a_2737_);
                v_subst_2744_ = crate::leanh::lean_ctor_get(v___x_2743_, 0);
                v_used_2745_ = crate::leanh::lean_ctor_get(v___x_2743_, 1);
                v_binderRenaming_2746_ = crate::leanh::lean_ctor_get(v___x_2743_, 2);
                v_funDeclInfoMap_2747_ = crate::leanh::lean_ctor_get(v___x_2743_, 3);
                v_simplified_2748_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2743_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2749_ = crate::leanh::lean_ctor_get(v___x_2743_, 4);
                v_inline_2750_ = crate::leanh::lean_ctor_get(v___x_2743_, 5);
                v_inlineLocal_2751_ = crate::leanh::lean_ctor_get(v___x_2743_, 6);
                v_isSharedCheck_2795_ = (!crate::leanh::lean_is_exclusive(v___x_2743_)) as u8;
                if v_isSharedCheck_2795_ == 0 {
                    v___x_2753_ = v___x_2743_;
                    v_isShared_2754_ = v_isSharedCheck_2795_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2751_);
                    crate::leanh::lean_inc(v_inline_2750_);
                    crate::leanh::lean_inc(v_visited_2749_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_2747_);
                    crate::leanh::lean_inc(v_binderRenaming_2746_);
                    crate::leanh::lean_inc(v_used_2745_);
                    crate::leanh::lean_inc(v_subst_2744_);
                    crate::leanh::lean_dec(v___x_2743_);
                    v___x_2753_ = crate::leanh::lean_box(0);
                    v_isShared_2754_ = v_isSharedCheck_2795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2755_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1,
                );
                if v_isShared_2754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2753_, 3, v___x_2755_);
                    v___x_2757_ = v___x_2753_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_subst_2744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_used_2745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_binderRenaming_2746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 3, v___x_2755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_visited_2749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 5, v_inline_2750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 6, v_inlineLocal_2751_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2794_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2748_,
                    );
                    v___x_2757_ = v_reuseFailAlloc_2794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2758_ = lean_st_ref_set(v_a_2737_, v___x_2757_);
                v___x_2759_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(
                    v_funDeclInfoMap_2747_,
                    v_code_2735_,
                    v_mustInline_2736_,
                    v_a_2738_,
                    v_a_2739_,
                    v_a_2740_,
                    v_a_2741_,
                );
                if crate::leanh::lean_obj_tag(v___x_2759_) == 0 {
                    v_a_2760_ = crate::leanh::lean_ctor_get(v___x_2759_, 0);
                    v_isSharedCheck_2785_ = (!crate::leanh::lean_is_exclusive(v___x_2759_)) as u8;
                    if v_isSharedCheck_2785_ == 0 {
                        v___x_2762_ = v___x_2759_;
                        v_isShared_2763_ = v_isSharedCheck_2785_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2760_);
                        crate::leanh::lean_dec(v___x_2759_);
                        v___x_2762_ = crate::leanh::lean_box(0);
                        v_isShared_2763_ = v_isSharedCheck_2785_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2786_ = crate::leanh::lean_ctor_get(v___x_2759_, 0);
                    v_isSharedCheck_2793_ = (!crate::leanh::lean_is_exclusive(v___x_2759_)) as u8;
                    if v_isSharedCheck_2793_ == 0 {
                        v___x_2788_ = v___x_2759_;
                        v_isShared_2789_ = v_isSharedCheck_2793_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2786_);
                        crate::leanh::lean_dec(v___x_2759_);
                        v___x_2788_ = crate::leanh::lean_box(0);
                        v_isShared_2789_ = v_isSharedCheck_2793_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2764_ = lean_st_ref_take(v_a_2737_);
                v_subst_2765_ = crate::leanh::lean_ctor_get(v___x_2764_, 0);
                v_used_2766_ = crate::leanh::lean_ctor_get(v___x_2764_, 1);
                v_binderRenaming_2767_ = crate::leanh::lean_ctor_get(v___x_2764_, 2);
                v_simplified_2768_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2764_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_2769_ = crate::leanh::lean_ctor_get(v___x_2764_, 4);
                v_inline_2770_ = crate::leanh::lean_ctor_get(v___x_2764_, 5);
                v_inlineLocal_2771_ = crate::leanh::lean_ctor_get(v___x_2764_, 6);
                v_isSharedCheck_2783_ = (!crate::leanh::lean_is_exclusive(v___x_2764_)) as u8;
                if v_isSharedCheck_2783_ == 0 {
                    v_unused_2784_ = crate::leanh::lean_ctor_get(v___x_2764_, 3);
                    crate::leanh::lean_dec(v_unused_2784_);
                    v___x_2773_ = v___x_2764_;
                    v_isShared_2774_ = v_isSharedCheck_2783_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_2771_);
                    crate::leanh::lean_inc(v_inline_2770_);
                    crate::leanh::lean_inc(v_visited_2769_);
                    crate::leanh::lean_inc(v_binderRenaming_2767_);
                    crate::leanh::lean_inc(v_used_2766_);
                    crate::leanh::lean_inc(v_subst_2765_);
                    crate::leanh::lean_dec(v___x_2764_);
                    v___x_2773_ = crate::leanh::lean_box(0);
                    v_isShared_2774_ = v_isSharedCheck_2783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2774_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2773_, 3, v_a_2760_);
                    v___x_2776_ = v___x_2773_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_subst_2765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_used_2766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 2, v_binderRenaming_2767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 3, v_a_2760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 4, v_visited_2769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 5, v_inline_2770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 6, v_inlineLocal_2771_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2782_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_2768_,
                    );
                    v___x_2776_ = v_reuseFailAlloc_2782_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2777_ = lean_st_ref_set(v_a_2737_, v___x_2776_);
                v___x_2778_ = crate::leanh::lean_box(0);
                if v_isShared_2763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2762_, 0, v___x_2778_);
                    v___x_2780_ = v___x_2762_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
                    v___x_2780_ = v_reuseFailAlloc_2781_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2780_;
            }
            7 => {
                if v_isShared_2789_ == 0 {
                    v___x_2791_ = v___x_2788_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
                    v___x_2791_ = v_reuseFailAlloc_2792_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___boxed(
    mut v_code_2796_: *mut crate::leanh::LeanObject,
    mut v_mustInline_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
    mut v_a_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_2804_: u8 = 0;
    let mut v_res_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_2804_ = (crate::leanh::lean_unbox(v_mustInline_2797_) as u8);
    v_res_2805_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
        v_code_2796_,
        v_mustInline_boxed_2804_,
        v_a_2798_,
        v_a_2799_,
        v_a_2800_,
        v_a_2801_,
        v_a_2802_,
    );
    crate::leanh::lean_dec(v_a_2802_);
    crate::leanh::lean_dec_ref(v_a_2801_);
    crate::leanh::lean_dec(v_a_2800_);
    crate::leanh::lean_dec_ref(v_a_2799_);
    crate::leanh::lean_dec(v_a_2798_);
    return v_res_2805_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(
    mut v_code_2806_: *mut crate::leanh::LeanObject,
    mut v_mustInline_2807_: u8,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
    mut v_a_2809_: *mut crate::leanh::LeanObject,
    mut v_a_2810_: *mut crate::leanh::LeanObject,
    mut v_a_2811_: *mut crate::leanh::LeanObject,
    mut v_a_2812_: *mut crate::leanh::LeanObject,
    mut v_a_2813_: *mut crate::leanh::LeanObject,
    mut v_a_2814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2816_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
        v_code_2806_,
        v_mustInline_2807_,
        v_a_2809_,
        v_a_2811_,
        v_a_2812_,
        v_a_2813_,
        v_a_2814_,
    );
    return v___x_2816_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___boxed(
    mut v_code_2817_: *mut crate::leanh::LeanObject,
    mut v_mustInline_2818_: *mut crate::leanh::LeanObject,
    mut v_a_2819_: *mut crate::leanh::LeanObject,
    mut v_a_2820_: *mut crate::leanh::LeanObject,
    mut v_a_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
    mut v_a_2823_: *mut crate::leanh::LeanObject,
    mut v_a_2824_: *mut crate::leanh::LeanObject,
    mut v_a_2825_: *mut crate::leanh::LeanObject,
    mut v_a_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_2827_: u8 = 0;
    let mut v_res_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_2827_ = (crate::leanh::lean_unbox(v_mustInline_2818_) as u8);
    v_res_2828_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(
        v_code_2817_,
        v_mustInline_boxed_2827_,
        v_a_2819_,
        v_a_2820_,
        v_a_2821_,
        v_a_2822_,
        v_a_2823_,
        v_a_2824_,
        v_a_2825_,
    );
    crate::leanh::lean_dec(v_a_2825_);
    crate::leanh::lean_dec_ref(v_a_2824_);
    crate::leanh::lean_dec(v_a_2823_);
    crate::leanh::lean_dec_ref(v_a_2822_);
    crate::leanh::lean_dec_ref(v_a_2821_);
    crate::leanh::lean_dec(v_a_2820_);
    crate::leanh::lean_dec_ref(v_a_2819_);
    return v_res_2828_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2829_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2830_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__0);
    v___x_2831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2831_, 0, v___x_2830_);
    return v___x_2831_;
}
pub unsafe fn _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__1);
    v___x_2833_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2834_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2834_, 0, v___x_2833_);
    crate::leanh::lean_ctor_set(v___x_2834_, 1, v___x_2833_);
    crate::leanh::lean_ctor_set(v___x_2834_, 2, v___x_2833_);
    crate::leanh::lean_ctor_set(v___x_2834_, 3, v___x_2833_);
    crate::leanh::lean_ctor_set(v___x_2834_, 4, v___x_2832_);
    crate::leanh::lean_ctor_set(v___x_2834_, 5, v___x_2832_);
    crate::leanh::lean_ctor_set(v___x_2834_, 6, v___x_2832_);
    crate::leanh::lean_ctor_set(v___x_2834_, 7, v___x_2832_);
    crate::leanh::lean_ctor_set(v___x_2834_, 8, v___x_2832_);
    crate::leanh::lean_ctor_set(v___x_2834_, 9, v___x_2832_);
    return v___x_2834_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(
    mut v_msg_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2849_: u8 = 0;
    let mut v_env_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2854_: u8 = 0;
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2866_: u8 = 0;
    let mut v_unused_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_a_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2841_ = crate::leanh::lean_ctor_get(v___y_2838_, 2);
                v_ref_2842_ = crate::leanh::lean_ctor_get(v___y_2838_, 5);
                v___x_2843_ = lean_st_ref_get(v___y_2839_);
                v___x_2844_ = lean_st_ref_get(v___y_2837_);
                v___x_2845_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2836_);
                if crate::leanh::lean_obj_tag(v___x_2845_) == 0 {
                    v_a_2846_ = crate::leanh::lean_ctor_get(v___x_2845_, 0);
                    v_isSharedCheck_2868_ = (!crate::leanh::lean_is_exclusive(v___x_2845_)) as u8;
                    if v_isSharedCheck_2868_ == 0 {
                        v___x_2848_ = v___x_2845_;
                        v_isShared_2849_ = v_isSharedCheck_2868_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2846_);
                        crate::leanh::lean_dec(v___x_2845_);
                        v___x_2848_ = crate::leanh::lean_box(0);
                        v_isShared_2849_ = v_isSharedCheck_2868_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2844_);
                    crate::leanh::lean_dec(v___x_2843_);
                    crate::leanh::lean_dec_ref(v_msg_2835_);
                    v_a_2869_ = crate::leanh::lean_ctor_get(v___x_2845_, 0);
                    v_isSharedCheck_2876_ = (!crate::leanh::lean_is_exclusive(v___x_2845_)) as u8;
                    if v_isSharedCheck_2876_ == 0 {
                        v___x_2871_ = v___x_2845_;
                        v_isShared_2872_ = v_isSharedCheck_2876_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2869_);
                        crate::leanh::lean_dec(v___x_2845_);
                        v___x_2871_ = crate::leanh::lean_box(0);
                        v_isShared_2872_ = v_isSharedCheck_2876_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_env_2850_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                crate::leanh::lean_inc_ref(v_env_2850_);
                crate::leanh::lean_dec(v___x_2843_);
                v_lctx_2851_ = crate::leanh::lean_ctor_get(v___x_2844_, 0);
                v_isSharedCheck_2866_ = (!crate::leanh::lean_is_exclusive(v___x_2844_)) as u8;
                if v_isSharedCheck_2866_ == 0 {
                    v_unused_2867_ = crate::leanh::lean_ctor_get(v___x_2844_, 1);
                    crate::leanh::lean_dec(v_unused_2867_);
                    v___x_2853_ = v___x_2844_;
                    v_isShared_2854_ = v_isSharedCheck_2866_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_2851_);
                    crate::leanh::lean_dec(v___x_2844_);
                    v___x_2853_ = crate::leanh::lean_box(0);
                    v_isShared_2854_ = v_isSharedCheck_2866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2855_ = (crate::leanh::lean_unbox(v_a_2846_) as u8);
                crate::leanh::lean_dec(v_a_2846_);
                v___x_2856_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2851_, v___x_2855_);
                crate::leanh::lean_dec_ref(v_lctx_2851_);
                v___x_2857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
                crate::leanh::lean_inc_ref(v_options_2841_);
                v___x_2858_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2858_, 0, v_env_2850_);
                crate::leanh::lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                crate::leanh::lean_ctor_set(v___x_2858_, 2, v___x_2856_);
                crate::leanh::lean_ctor_set(v___x_2858_, 3, v_options_2841_);
                if v_isShared_2854_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2853_, 3);
                    crate::leanh::lean_ctor_set(v___x_2853_, 1, v_msg_2835_);
                    crate::leanh::lean_ctor_set(v___x_2853_, 0, v___x_2858_);
                    v___x_2860_ = v___x_2853_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2865_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_msg_2835_);
                    v___x_2860_ = v_reuseFailAlloc_2865_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_2842_);
                v___x_2861_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2861_, 0, v_ref_2842_);
                crate::leanh::lean_ctor_set(v___x_2861_, 1, v___x_2860_);
                if v_isShared_2849_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2848_, 1);
                    crate::leanh::lean_ctor_set(v___x_2848_, 0, v___x_2861_);
                    v___x_2863_ = v___x_2848_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2863_;
            }
            5 => {
                if v_isShared_2872_ == 0 {
                    v___x_2874_ = v___x_2871_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___boxed(
    mut v_msg_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2883_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
    crate::leanh::lean_dec(v___y_2881_);
    crate::leanh::lean_dec_ref(v___y_2880_);
    crate::leanh::lean_dec(v___y_2879_);
    crate::leanh::lean_dec_ref(v___y_2878_);
    return v_res_2883_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(
    mut v_00_u03b1_2884_: *mut crate::leanh::LeanObject,
    mut v_msg_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2894_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v_msg_2885_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
    return v___x_2894_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___boxed(
    mut v_00_u03b1_2895_: *mut crate::leanh::LeanObject,
    mut v_msg_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
    mut v___y_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2905_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0(v_00_u03b1_2895_, v_msg_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
    crate::leanh::lean_dec(v___y_2903_);
    crate::leanh::lean_dec_ref(v___y_2902_);
    crate::leanh::lean_dec(v___y_2901_);
    crate::leanh::lean_dec_ref(v___y_2900_);
    crate::leanh::lean_dec_ref(v___y_2899_);
    crate::leanh::lean_dec(v___y_2898_);
    crate::leanh::lean_dec_ref(v___y_2897_);
    return v_res_2905_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: f64 = 0.0;
    v___x_2906_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2907_ = lean_float_of_nat(v___x_2906_);
    return v___x_2907_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(
    mut v_cls_2911_: *mut crate::leanh::LeanObject,
    mut v_msg_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2926_: u8 = 0;
    let mut v_env_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v_tid_2946_: u64 = 0;
    let mut v_traces_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: f64 = 0.0;
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut v_isSharedCheck_2979_: u8 = 0;
    let mut v_unused_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2981_: u8 = 0;
    let mut v_a_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2918_ = crate::leanh::lean_ctor_get(v___y_2915_, 2);
                v_ref_2919_ = crate::leanh::lean_ctor_get(v___y_2915_, 5);
                v___x_2920_ = lean_st_ref_get(v___y_2916_);
                v___x_2921_ = lean_st_ref_get(v___y_2914_);
                v___x_2922_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_2913_);
                if crate::leanh::lean_obj_tag(v___x_2922_) == 0 {
                    v_a_2923_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2981_ = (!crate::leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2981_ == 0 {
                        v___x_2925_ = v___x_2922_;
                        v_isShared_2926_ = v_isSharedCheck_2981_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2923_);
                        crate::leanh::lean_dec(v___x_2922_);
                        v___x_2925_ = crate::leanh::lean_box(0);
                        v_isShared_2926_ = v_isSharedCheck_2981_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2921_);
                    crate::leanh::lean_dec(v___x_2920_);
                    crate::leanh::lean_dec_ref(v_msg_2912_);
                    crate::leanh::lean_dec(v_cls_2911_);
                    v_a_2982_ = crate::leanh::lean_ctor_get(v___x_2922_, 0);
                    v_isSharedCheck_2989_ = (!crate::leanh::lean_is_exclusive(v___x_2922_)) as u8;
                    if v_isSharedCheck_2989_ == 0 {
                        v___x_2984_ = v___x_2922_;
                        v_isShared_2985_ = v_isSharedCheck_2989_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2982_);
                        crate::leanh::lean_dec(v___x_2922_);
                        v___x_2984_ = crate::leanh::lean_box(0);
                        v_isShared_2985_ = v_isSharedCheck_2989_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_2927_ = crate::leanh::lean_ctor_get(v___x_2920_, 0);
                crate::leanh::lean_inc_ref(v_env_2927_);
                crate::leanh::lean_dec(v___x_2920_);
                v_lctx_2928_ = crate::leanh::lean_ctor_get(v___x_2921_, 0);
                v_isSharedCheck_2979_ = (!crate::leanh::lean_is_exclusive(v___x_2921_)) as u8;
                if v_isSharedCheck_2979_ == 0 {
                    v_unused_2980_ = crate::leanh::lean_ctor_get(v___x_2921_, 1);
                    crate::leanh::lean_dec(v_unused_2980_);
                    v___x_2930_ = v___x_2921_;
                    v_isShared_2931_ = v_isSharedCheck_2979_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_2928_);
                    crate::leanh::lean_dec(v___x_2921_);
                    v___x_2930_ = crate::leanh::lean_box(0);
                    v_isShared_2931_ = v_isSharedCheck_2979_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2_once), _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg___closed__2);
                v___x_2933_ = lean_st_ref_take(v___y_2916_);
                v_traceState_2934_ = crate::leanh::lean_ctor_get(v___x_2933_, 4);
                v_env_2935_ = crate::leanh::lean_ctor_get(v___x_2933_, 0);
                v_nextMacroScope_2936_ = crate::leanh::lean_ctor_get(v___x_2933_, 1);
                v_ngen_2937_ = crate::leanh::lean_ctor_get(v___x_2933_, 2);
                v_auxDeclNGen_2938_ = crate::leanh::lean_ctor_get(v___x_2933_, 3);
                v_cache_2939_ = crate::leanh::lean_ctor_get(v___x_2933_, 5);
                v_messages_2940_ = crate::leanh::lean_ctor_get(v___x_2933_, 6);
                v_infoState_2941_ = crate::leanh::lean_ctor_get(v___x_2933_, 7);
                v_snapshotTasks_2942_ = crate::leanh::lean_ctor_get(v___x_2933_, 8);
                v_isSharedCheck_2978_ = (!crate::leanh::lean_is_exclusive(v___x_2933_)) as u8;
                if v_isSharedCheck_2978_ == 0 {
                    v___x_2944_ = v___x_2933_;
                    v_isShared_2945_ = v_isSharedCheck_2978_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2942_);
                    crate::leanh::lean_inc(v_infoState_2941_);
                    crate::leanh::lean_inc(v_messages_2940_);
                    crate::leanh::lean_inc(v_cache_2939_);
                    crate::leanh::lean_inc(v_traceState_2934_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2938_);
                    crate::leanh::lean_inc(v_ngen_2937_);
                    crate::leanh::lean_inc(v_nextMacroScope_2936_);
                    crate::leanh::lean_inc(v_env_2935_);
                    crate::leanh::lean_dec(v___x_2933_);
                    v___x_2944_ = crate::leanh::lean_box(0);
                    v_isShared_2945_ = v_isSharedCheck_2978_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_2946_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2947_ = crate::leanh::lean_ctor_get(v_traceState_2934_, 0);
                v_isSharedCheck_2977_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2934_)) as u8;
                if v_isSharedCheck_2977_ == 0 {
                    v___x_2949_ = v_traceState_2934_;
                    v_isShared_2950_ = v_isSharedCheck_2977_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2947_);
                    crate::leanh::lean_dec(v_traceState_2934_);
                    v___x_2949_ = crate::leanh::lean_box(0);
                    v_isShared_2950_ = v_isSharedCheck_2977_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2951_ = (crate::leanh::lean_unbox(v_a_2923_) as u8);
                crate::leanh::lean_dec(v_a_2923_);
                v___x_2952_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_2928_, v___x_2951_);
                crate::leanh::lean_dec_ref(v_lctx_2928_);
                crate::leanh::lean_inc_ref(v_options_2918_);
                v___x_2953_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2953_, 0, v_env_2927_);
                crate::leanh::lean_ctor_set(v___x_2953_, 1, v___x_2932_);
                crate::leanh::lean_ctor_set(v___x_2953_, 2, v___x_2952_);
                crate::leanh::lean_ctor_set(v___x_2953_, 3, v_options_2918_);
                if v_isShared_2931_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2930_, 3);
                    crate::leanh::lean_ctor_set(v___x_2930_, 1, v_msg_2912_);
                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2953_);
                    v___x_2955_ = v___x_2930_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2976_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_msg_2912_);
                    v___x_2955_ = v_reuseFailAlloc_2976_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2956_ = crate::leanh::lean_box(0);
                v___x_2957_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__0);
                v___x_2958_ = 0;
                v___x_2959_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__1;
                v___x_2960_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2960_, 0, v_cls_2911_);
                crate::leanh::lean_ctor_set(v___x_2960_, 1, v___x_2956_);
                crate::leanh::lean_ctor_set(v___x_2960_, 2, v___x_2959_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2960_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2957_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2960_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2957_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2960_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2958_,
                );
                v___x_2961_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___closed__2;
                v___x_2962_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2962_, 0, v___x_2960_);
                crate::leanh::lean_ctor_set(v___x_2962_, 1, v___x_2955_);
                crate::leanh::lean_ctor_set(v___x_2962_, 2, v___x_2961_);
                crate::leanh::lean_inc(v_ref_2919_);
                v___x_2963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2963_, 0, v_ref_2919_);
                crate::leanh::lean_ctor_set(v___x_2963_, 1, v___x_2962_);
                v___x_2964_ = l_Lean_PersistentArray_push___redArg(v_traces_2947_, v___x_2963_);
                if v_isShared_2950_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2949_, 0, v___x_2964_);
                    v___x_2966_ = v___x_2949_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2964_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2975_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2946_,
                    );
                    v___x_2966_ = v_reuseFailAlloc_2975_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2944_, 4, v___x_2966_);
                    v___x_2968_ = v___x_2944_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_env_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_nextMacroScope_2936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_ngen_2937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_auxDeclNGen_2938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 4, v___x_2966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 5, v_cache_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 6, v_messages_2940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 7, v_infoState_2941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 8, v_snapshotTasks_2942_);
                    v___x_2968_ = v_reuseFailAlloc_2974_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2969_ = lean_st_ref_set(v___y_2916_, v___x_2968_);
                v___x_2970_ = crate::leanh::lean_box(0);
                if v_isShared_2926_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2925_, 0, v___x_2970_);
                    v___x_2972_ = v___x_2925_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2972_;
            }
            9 => {
                if v_isShared_2985_ == 0 {
                    v___x_2987_ = v___x_2984_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
                    v___x_2987_ = v_reuseFailAlloc_2988_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg___boxed(
    mut v_cls_2990_: *mut crate::leanh::LeanObject,
    mut v_msg_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_2990_, v_msg_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
    crate::leanh::lean_dec(v___y_2995_);
    crate::leanh::lean_dec_ref(v___y_2994_);
    crate::leanh::lean_dec(v___y_2993_);
    crate::leanh::lean_dec_ref(v___y_2992_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(
    mut v_cls_2998_: *mut crate::leanh::LeanObject,
    mut v_msg_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
    mut v___y_3003_: *mut crate::leanh::LeanObject,
    mut v___y_3004_: *mut crate::leanh::LeanObject,
    mut v___y_3005_: *mut crate::leanh::LeanObject,
    mut v___y_3006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_2998_, v_msg_2999_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
    return v___x_3008_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___boxed(
    mut v_cls_3009_: *mut crate::leanh::LeanObject,
    mut v_msg_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
    mut v___y_3015_: *mut crate::leanh::LeanObject,
    mut v___y_3016_: *mut crate::leanh::LeanObject,
    mut v___y_3017_: *mut crate::leanh::LeanObject,
    mut v___y_3018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3019_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2(v_cls_3009_, v_msg_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
    crate::leanh::lean_dec(v___y_3017_);
    crate::leanh::lean_dec_ref(v___y_3016_);
    crate::leanh::lean_dec(v___y_3015_);
    crate::leanh::lean_dec_ref(v___y_3014_);
    crate::leanh::lean_dec_ref(v___y_3013_);
    crate::leanh::lean_dec(v___y_3012_);
    crate::leanh::lean_dec_ref(v___y_3011_);
    return v_res_3019_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(
    mut v_keys_3020_: *mut crate::leanh::LeanObject,
    mut v_vals_3021_: *mut crate::leanh::LeanObject,
    mut v_i_3022_: *mut crate::leanh::LeanObject,
    mut v_k_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3024_ = lean_array_get_size(v_keys_3020_);
                v___x_3025_ = lean_nat_dec_lt(v_i_3022_, v___x_3024_);
                if v___x_3025_ == 0 {
                    crate::leanh::lean_dec(v_i_3022_);
                    v___x_3026_ = crate::leanh::lean_box(0);
                    return v___x_3026_;
                } else {
                    v_k_x27_3027_ = lean_array_fget_borrowed(v_keys_3020_, v_i_3022_);
                    v___x_3028_ = lean_name_eq(v_k_3023_, v_k_x27_3027_);
                    if v___x_3028_ == 0 {
                        v___x_3029_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3030_ = lean_nat_add(v_i_3022_, v___x_3029_);
                        crate::leanh::lean_dec(v_i_3022_);
                        v_i_3022_ = v___x_3030_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3032_ = lean_array_fget_borrowed(v_vals_3021_, v_i_3022_);
                        crate::leanh::lean_dec(v_i_3022_);
                        crate::leanh::lean_inc(v___x_3032_);
                        v___x_3033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3033_, 0, v___x_3032_);
                        return v___x_3033_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_keys_3034_: *mut crate::leanh::LeanObject,
    mut v_vals_3035_: *mut crate::leanh::LeanObject,
    mut v_i_3036_: *mut crate::leanh::LeanObject,
    mut v_k_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3038_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_3034_, v_vals_3035_, v_i_3036_, v_k_3037_);
    crate::leanh::lean_dec(v_k_3037_);
    crate::leanh::lean_dec_ref(v_vals_3035_);
    crate::leanh::lean_dec_ref(v_keys_3034_);
    return v_res_3038_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_3039_: usize = 0;
    let mut v___x_3040_: usize = 0;
    let mut v___x_3041_: usize = 0;
    v___x_3039_ = 5usize;
    v___x_3040_ = 1usize;
    v___x_3041_ = lean_usize_shift_left(v___x_3040_, v___x_3039_);
    return v___x_3041_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_3042_: usize = 0;
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: usize = 0;
    v___x_3042_ = 1usize;
    v___x_3043_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__0);
    v___x_3044_ = lean_usize_sub(v___x_3043_, v___x_3042_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(
    mut v_x_3045_: *mut crate::leanh::LeanObject,
    mut v_x_3046_: usize,
    mut v_x_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: usize = 0;
    let mut v___x_3051_: usize = 0;
    let mut v___x_3052_: usize = 0;
    let mut v_j_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: usize = 0;
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3045_) == 0 {
                    v_es_3048_ = crate::leanh::lean_ctor_get(v_x_3045_, 0);
                    v___x_3049_ = crate::leanh::lean_box(2);
                    v___x_3050_ = 5usize;
                    v___x_3051_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___closed__1);
                    v___x_3052_ = lean_usize_land(v_x_3046_, v___x_3051_);
                    v_j_3053_ = lean_usize_to_nat(v___x_3052_);
                    v___x_3054_ = lean_array_get_borrowed(v___x_3049_, v_es_3048_, v_j_3053_);
                    crate::leanh::lean_dec(v_j_3053_);
                    match crate::leanh::lean_obj_tag(v___x_3054_) {
                        0 => {
                            v_key_3055_ = crate::leanh::lean_ctor_get(v___x_3054_, 0);
                            v_val_3056_ = crate::leanh::lean_ctor_get(v___x_3054_, 1);
                            v___x_3057_ = lean_name_eq(v_x_3047_, v_key_3055_);
                            if v___x_3057_ == 0 {
                                v___x_3058_ = crate::leanh::lean_box(0);
                                return v___x_3058_;
                            } else {
                                crate::leanh::lean_inc(v_val_3056_);
                                v___x_3059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3059_, 0, v_val_3056_);
                                return v___x_3059_;
                            }
                        }
                        1 => {
                            v_node_3060_ = crate::leanh::lean_ctor_get(v___x_3054_, 0);
                            v___x_3061_ = lean_usize_shift_right(v_x_3046_, v___x_3050_);
                            v_x_3045_ = v_node_3060_;
                            v_x_3046_ = v___x_3061_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3063_ = crate::leanh::lean_box(0);
                            return v___x_3063_;
                        }
                    }
                } else {
                    v_ks_3064_ = crate::leanh::lean_ctor_get(v_x_3045_, 0);
                    v_vs_3065_ = crate::leanh::lean_ctor_get(v_x_3045_, 1);
                    v___x_3066_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3067_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_ks_3064_, v_vs_3065_, v___x_3066_, v_x_3047_);
                    return v___x_3067_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg___boxed(
    mut v_x_3068_: *mut crate::leanh::LeanObject,
    mut v_x_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7620__boxed_3071_: usize = 0;
    let mut v_res_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7620__boxed_3071_ = crate::leanh::lean_unbox_usize(v_x_3069_);
    crate::leanh::lean_dec(v_x_3069_);
    v_res_3072_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_3068_, v_x_7620__boxed_3071_, v_x_3070_);
    crate::leanh::lean_dec(v_x_3070_);
    crate::leanh::lean_dec_ref(v_x_3068_);
    return v_res_3072_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u64 = 0;
    v___x_3073_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3074_ = lean_uint64_of_nat(v___x_3073_);
    return v___x_3074_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(
    mut v_x_3075_: *mut crate::leanh::LeanObject,
    mut v_x_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3078_: u64 = 0;
    let mut v___x_3079_: usize = 0;
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u64 = 0;
    let mut v_hash_3082_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3076_) == 0 {
                    v___x_3081_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___closed__0);
                    v___y_3078_ = v___x_3081_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3082_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_3076_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3078_ = v_hash_3082_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3079_ = lean_uint64_to_usize(v___y_3078_);
                v___x_3080_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_3075_, v___x_3079_, v_x_3076_);
                return v___x_3080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg___boxed(
    mut v_x_3083_: *mut crate::leanh::LeanObject,
    mut v_x_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_3083_, v_x_3084_);
    crate::leanh::lean_dec(v_x_3084_);
    crate::leanh::lean_dec_ref(v_x_3083_);
    return v_res_3085_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3087_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__0;
    v___x_3088_ = l_Lean_stringToMessageData(v___x_3087_);
    return v___x_3088_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__2;
    v___x_3091_ = l_Lean_stringToMessageData(v___x_3090_);
    return v___x_3091_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__4;
    v___x_3094_ = l_Lean_stringToMessageData(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_3105_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9;
    v___x_3106_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__11;
    v___x_3107_ = l_Lean_Name_append(v___x_3106_, v_cls_3105_);
    return v___x_3107_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(
    mut v_recursive_3108_: u8,
    mut v_declName_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineIfReduce_3120_: u8 = 0;
    let mut v___y_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v_unused_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3139_: u8 = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut v_unused_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v_maxRecInlineIfReduce_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecInlineIfReduce_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_a_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v___y_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: u8 = 0;
    let mut v_a_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3221_: u8 = 0;
    let mut v_a_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3229_: u8 = 0;
    let mut v___y_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStackOccs_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3243_: u8 = 0;
    let mut v_inheritedTraceOptions_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3254_: u8 = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3258_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3242_ = crate::leanh::lean_ctor_get(v_a_3115_, 2);
                v_hasTrace_3243_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3242_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3243_ == 0 {
                    v___y_3231_ = v_a_3110_;
                    v___y_3232_ = v_a_3111_;
                    v___y_3233_ = v_a_3112_;
                    v___y_3234_ = v_a_3113_;
                    v___y_3235_ = v_a_3114_;
                    v___y_3236_ = v_a_3115_;
                    v___y_3237_ = v_a_3116_;
                    state = 19;
                    continue;
                } else {
                    v_inheritedTraceOptions_3244_ = crate::leanh::lean_ctor_get(v_a_3115_, 13);
                    v_cls_3245_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__9;
                    v___x_3246_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__12);
                    v___x_3247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3244_,
                        v_options_3242_,
                        v___x_3246_,
                    );
                    if v___x_3247_ == 0 {
                        v___y_3231_ = v_a_3110_;
                        v___y_3232_ = v_a_3111_;
                        v___y_3233_ = v_a_3112_;
                        v___y_3234_ = v_a_3113_;
                        v___y_3235_ = v_a_3114_;
                        v___y_3236_ = v_a_3115_;
                        v___y_3237_ = v_a_3116_;
                        state = 19;
                        continue;
                    } else {
                        v___x_3248_ = 0;
                        crate::leanh::lean_inc(v_declName_3109_);
                        v___x_3249_ = l_Lean_MessageData_ofConstName(v_declName_3109_, v___x_3248_);
                        v___x_3250_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(v_cls_3245_, v___x_3249_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
                        if crate::leanh::lean_obj_tag(v___x_3250_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3250_, 1);
                            v___y_3231_ = v_a_3110_;
                            v___y_3232_ = v_a_3111_;
                            v___y_3233_ = v_a_3112_;
                            v___y_3234_ = v_a_3113_;
                            v___y_3235_ = v_a_3114_;
                            v___y_3236_ = v_a_3115_;
                            v___y_3237_ = v_a_3116_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_declName_3109_);
                            v_a_3251_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                            v_isSharedCheck_3258_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3250_)) as u8;
                            if v_isSharedCheck_3258_ == 0 {
                                v___x_3253_ = v___x_3250_;
                                v_isShared_3254_ = v_isSharedCheck_3258_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3251_);
                                crate::leanh::lean_dec(v___x_3250_);
                                v___x_3253_ = crate::leanh::lean_box(0);
                                v_isShared_3254_ = v_isSharedCheck_3258_;
                                state = 20;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3128_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_3124_);
                if crate::leanh::lean_obj_tag(v___x_3128_) == 0 {
                    if v_recursive_3108_ == 0 {
                        crate::leanh::lean_dec(v_declName_3109_);
                        v_isSharedCheck_3135_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3128_)) as u8;
                        if v_isSharedCheck_3135_ == 0 {
                            v_unused_3136_ = crate::leanh::lean_ctor_get(v___x_3128_, 0);
                            crate::leanh::lean_dec(v_unused_3136_);
                            v___x_3130_ = v___x_3128_;
                            v_isShared_3131_ = v_isSharedCheck_3135_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3128_);
                            v___x_3130_ = crate::leanh::lean_box(0);
                            v_isShared_3131_ = v_isSharedCheck_3135_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_inlineIfReduce_3120_ == 0 {
                            crate::leanh::lean_dec(v_declName_3109_);
                            v_isSharedCheck_3143_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3128_)) as u8;
                            if v_isSharedCheck_3143_ == 0 {
                                v_unused_3144_ = crate::leanh::lean_ctor_get(v___x_3128_, 0);
                                crate::leanh::lean_dec(v_unused_3144_);
                                v___x_3138_ = v___x_3128_;
                                v_isShared_3139_ = v_isSharedCheck_3143_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3128_);
                                v___x_3138_ = crate::leanh::lean_box(0);
                                v_isShared_3139_ = v_isSharedCheck_3143_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_3145_ = crate::leanh::lean_ctor_get(v___x_3128_, 0);
                            v_isSharedCheck_3186_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3128_)) as u8;
                            if v_isSharedCheck_3186_ == 0 {
                                v___x_3147_ = v___x_3128_;
                                v_isShared_3148_ = v_isSharedCheck_3186_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3145_);
                                crate::leanh::lean_dec(v___x_3128_);
                                v___x_3147_ = crate::leanh::lean_box(0);
                                v_isShared_3148_ = v_isSharedCheck_3186_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3119_);
                    crate::leanh::lean_dec(v_declName_3109_);
                    v_a_3187_ = crate::leanh::lean_ctor_get(v___x_3128_, 0);
                    v_isSharedCheck_3194_ = (!crate::leanh::lean_is_exclusive(v___x_3128_)) as u8;
                    if v_isSharedCheck_3194_ == 0 {
                        v___x_3189_ = v___x_3128_;
                        v_isShared_3190_ = v_isSharedCheck_3194_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3187_);
                        crate::leanh::lean_dec(v___x_3128_);
                        v___x_3189_ = crate::leanh::lean_box(0);
                        v_isShared_3190_ = v_isSharedCheck_3194_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3131_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3130_, 0, v___y_3119_);
                    v___x_3133_ = v___x_3130_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___y_3119_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3133_;
            }
            4 => {
                if v_isShared_3139_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3138_, 0, v___y_3119_);
                    v___x_3141_ = v___x_3138_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___y_3119_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3141_;
            }
            6 => {
                v_maxRecInlineIfReduce_3149_ = crate::leanh::lean_ctor_get(v_a_3145_, 2);
                crate::leanh::lean_inc(v_maxRecInlineIfReduce_3149_);
                crate::leanh::lean_dec(v_a_3145_);
                v___x_3150_ = lean_nat_dec_lt(v_maxRecInlineIfReduce_3149_, v___y_3119_);
                crate::leanh::lean_dec(v_maxRecInlineIfReduce_3149_);
                if v___x_3150_ == 0 {
                    crate::leanh::lean_dec(v_declName_3109_);
                    if v_isShared_3148_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3147_, 0, v___y_3119_);
                        v___x_3152_ = v___x_3147_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___y_3119_);
                        v___x_3152_ = v_reuseFailAlloc_3153_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3147_);
                    crate::leanh::lean_dec(v___y_3119_);
                    v___x_3154_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_3124_);
                    if crate::leanh::lean_obj_tag(v___x_3154_) == 0 {
                        v_a_3155_ = crate::leanh::lean_ctor_get(v___x_3154_, 0);
                        crate::leanh::lean_inc(v_a_3155_);
                        crate::leanh::lean_dec_ref_known(v___x_3154_, 1);
                        v_maxRecInlineIfReduce_3156_ = crate::leanh::lean_ctor_get(v_a_3155_, 2);
                        crate::leanh::lean_inc(v_maxRecInlineIfReduce_3156_);
                        crate::leanh::lean_dec(v_a_3155_);
                        v___x_3157_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__1);
                        v___x_3158_ = 0;
                        v___x_3159_ = l_Lean_MessageData_ofConstName(v_declName_3109_, v___x_3158_);
                        v___x_3160_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3160_, 0, v___x_3157_);
                        crate::leanh::lean_ctor_set(v___x_3160_, 1, v___x_3159_);
                        v___x_3161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__3);
                        v___x_3162_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3162_, 0, v___x_3160_);
                        crate::leanh::lean_ctor_set(v___x_3162_, 1, v___x_3161_);
                        v___x_3163_ = l_Nat_reprFast(v_maxRecInlineIfReduce_3156_);
                        v___x_3164_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3164_, 0, v___x_3163_);
                        v___x_3165_ = l_Lean_MessageData_ofFormat(v___x_3164_);
                        v___x_3166_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3162_);
                        crate::leanh::lean_ctor_set(v___x_3166_, 1, v___x_3165_);
                        v___x_3167_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___closed__5);
                        v___x_3168_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3168_, 0, v___x_3166_);
                        crate::leanh::lean_ctor_set(v___x_3168_, 1, v___x_3167_);
                        v___x_3169_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_3168_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
                        v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3169_, 0);
                        v_isSharedCheck_3177_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3169_)) as u8;
                        if v_isSharedCheck_3177_ == 0 {
                            v___x_3172_ = v___x_3169_;
                            v_isShared_3173_ = v_isSharedCheck_3177_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3170_);
                            crate::leanh::lean_dec(v___x_3169_);
                            v___x_3172_ = crate::leanh::lean_box(0);
                            v_isShared_3173_ = v_isSharedCheck_3177_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_3109_);
                        v_a_3178_ = crate::leanh::lean_ctor_get(v___x_3154_, 0);
                        v_isSharedCheck_3185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3154_)) as u8;
                        if v_isSharedCheck_3185_ == 0 {
                            v___x_3180_ = v___x_3154_;
                            v_isShared_3181_ = v_isSharedCheck_3185_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3178_);
                            crate::leanh::lean_dec(v___x_3154_);
                            v___x_3180_ = crate::leanh::lean_box(0);
                            v_isShared_3181_ = v_isSharedCheck_3185_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_3152_;
            }
            8 => {
                if v_isShared_3173_ == 0 {
                    v___x_3175_ = v___x_3172_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
                    v___x_3175_ = v_reuseFailAlloc_3176_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3175_;
            }
            10 => {
                if v_isShared_3181_ == 0 {
                    v___x_3183_ = v___x_3180_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3183_;
            }
            12 => {
                if v_isShared_3190_ == 0 {
                    v___x_3192_ = v___x_3189_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
                    v___x_3192_ = v_reuseFailAlloc_3193_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3192_;
            }
            14 => {
                v___x_3204_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_3202_);
                if crate::leanh::lean_obj_tag(v___x_3204_) == 0 {
                    v_a_3205_ = crate::leanh::lean_ctor_get(v___x_3204_, 0);
                    crate::leanh::lean_inc(v_a_3205_);
                    crate::leanh::lean_dec_ref_known(v___x_3204_, 1);
                    v___x_3206_ = (crate::leanh::lean_unbox(v_a_3205_) as u8);
                    crate::leanh::lean_dec(v_a_3205_);
                    crate::leanh::lean_inc(v_declName_3109_);
                    v___x_3207_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                        v_declName_3109_,
                        v___x_3206_,
                        v___y_3200_,
                        v___y_3197_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3207_) == 0 {
                        v_a_3208_ = crate::leanh::lean_ctor_get(v___x_3207_, 0);
                        crate::leanh::lean_inc(v_a_3208_);
                        crate::leanh::lean_dec_ref_known(v___x_3207_, 1);
                        v___x_3209_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3210_ = lean_nat_add(v___y_3203_, v___x_3209_);
                        crate::leanh::lean_dec(v___y_3203_);
                        if crate::leanh::lean_obj_tag(v_a_3208_) == 1 {
                            v_val_3211_ = crate::leanh::lean_ctor_get(v_a_3208_, 0);
                            crate::leanh::lean_inc(v_val_3211_);
                            crate::leanh::lean_dec_ref_known(v_a_3208_, 1);
                            v___x_3212_ =
                                l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(v_val_3211_);
                            crate::leanh::lean_dec(v_val_3211_);
                            v___y_3119_ = v___x_3210_;
                            v_inlineIfReduce_3120_ = v___x_3212_;
                            v___y_3121_ = v___y_3196_;
                            v___y_3122_ = v___y_3198_;
                            v___y_3123_ = v___y_3199_;
                            v___y_3124_ = v___y_3202_;
                            v___y_3125_ = v___y_3201_;
                            v___y_3126_ = v___y_3200_;
                            v___y_3127_ = v___y_3197_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3208_);
                            v___x_3213_ = 0;
                            v___y_3119_ = v___x_3210_;
                            v_inlineIfReduce_3120_ = v___x_3213_;
                            v___y_3121_ = v___y_3196_;
                            v___y_3122_ = v___y_3198_;
                            v___y_3123_ = v___y_3199_;
                            v___y_3124_ = v___y_3202_;
                            v___y_3125_ = v___y_3201_;
                            v___y_3126_ = v___y_3200_;
                            v___y_3127_ = v___y_3197_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3203_);
                        crate::leanh::lean_dec(v_declName_3109_);
                        v_a_3214_ = crate::leanh::lean_ctor_get(v___x_3207_, 0);
                        v_isSharedCheck_3221_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3207_)) as u8;
                        if v_isSharedCheck_3221_ == 0 {
                            v___x_3216_ = v___x_3207_;
                            v_isShared_3217_ = v_isSharedCheck_3221_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3214_);
                            crate::leanh::lean_dec(v___x_3207_);
                            v___x_3216_ = crate::leanh::lean_box(0);
                            v_isShared_3217_ = v_isSharedCheck_3221_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3203_);
                    crate::leanh::lean_dec(v_declName_3109_);
                    v_a_3222_ = crate::leanh::lean_ctor_get(v___x_3204_, 0);
                    v_isSharedCheck_3229_ = (!crate::leanh::lean_is_exclusive(v___x_3204_)) as u8;
                    if v_isSharedCheck_3229_ == 0 {
                        v___x_3224_ = v___x_3204_;
                        v_isShared_3225_ = v_isSharedCheck_3229_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3222_);
                        crate::leanh::lean_dec(v___x_3204_);
                        v___x_3224_ = crate::leanh::lean_box(0);
                        v_isShared_3225_ = v_isSharedCheck_3229_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_3217_ == 0 {
                    v___x_3219_ = v___x_3216_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
                    v___x_3219_ = v_reuseFailAlloc_3220_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3219_;
            }
            17 => {
                if v_isShared_3225_ == 0 {
                    v___x_3227_ = v___x_3224_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
                    v___x_3227_ = v_reuseFailAlloc_3228_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3227_;
            }
            19 => {
                v_inlineStackOccs_3238_ = crate::leanh::lean_ctor_get(v___y_3231_, 3);
                v___x_3239_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_inlineStackOccs_3238_, v_declName_3109_);
                if crate::leanh::lean_obj_tag(v___x_3239_) == 0 {
                    v___x_3240_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3196_ = v___y_3231_;
                    v___y_3197_ = v___y_3237_;
                    v___y_3198_ = v___y_3232_;
                    v___y_3199_ = v___y_3233_;
                    v___y_3200_ = v___y_3236_;
                    v___y_3201_ = v___y_3235_;
                    v___y_3202_ = v___y_3234_;
                    v___y_3203_ = v___x_3240_;
                    state = 14;
                    continue;
                } else {
                    v_val_3241_ = crate::leanh::lean_ctor_get(v___x_3239_, 0);
                    crate::leanh::lean_inc(v_val_3241_);
                    crate::leanh::lean_dec_ref_known(v___x_3239_, 1);
                    v___y_3196_ = v___y_3231_;
                    v___y_3197_ = v___y_3237_;
                    v___y_3198_ = v___y_3232_;
                    v___y_3199_ = v___y_3233_;
                    v___y_3200_ = v___y_3236_;
                    v___y_3201_ = v___y_3235_;
                    v___y_3202_ = v___y_3234_;
                    v___y_3203_ = v_val_3241_;
                    state = 14;
                    continue;
                }
            }
            20 => {
                if v_isShared_3254_ == 0 {
                    v___x_3256_ = v___x_3253_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
                    v___x_3256_ = v_reuseFailAlloc_3257_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check___boxed(
    mut v_recursive_3259_: *mut crate::leanh::LeanObject,
    mut v_declName_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
    mut v_a_3264_: *mut crate::leanh::LeanObject,
    mut v_a_3265_: *mut crate::leanh::LeanObject,
    mut v_a_3266_: *mut crate::leanh::LeanObject,
    mut v_a_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recursive_boxed_3269_: u8 = 0;
    let mut v_res_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_recursive_boxed_3269_ = (crate::leanh::lean_unbox(v_recursive_3259_) as u8);
    v_res_3270_ =
        l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(
            v_recursive_boxed_3269_,
            v_declName_3260_,
            v_a_3261_,
            v_a_3262_,
            v_a_3263_,
            v_a_3264_,
            v_a_3265_,
            v_a_3266_,
            v_a_3267_,
        );
    crate::leanh::lean_dec(v_a_3267_);
    crate::leanh::lean_dec_ref(v_a_3266_);
    crate::leanh::lean_dec(v_a_3265_);
    crate::leanh::lean_dec_ref(v_a_3264_);
    crate::leanh::lean_dec_ref(v_a_3263_);
    crate::leanh::lean_dec(v_a_3262_);
    crate::leanh::lean_dec_ref(v_a_3261_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(
    mut v_00_u03b2_3271_: *mut crate::leanh::LeanObject,
    mut v_x_3272_: *mut crate::leanh::LeanObject,
    mut v_x_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(v_x_3272_, v_x_3273_);
    return v___x_3274_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___boxed(
    mut v_00_u03b2_3275_: *mut crate::leanh::LeanObject,
    mut v_x_3276_: *mut crate::leanh::LeanObject,
    mut v_x_3277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3278_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1(v_00_u03b2_3275_, v_x_3276_, v_x_3277_);
    crate::leanh::lean_dec(v_x_3277_);
    crate::leanh::lean_dec_ref(v_x_3276_);
    return v_res_3278_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(
    mut v_00_u03b2_3279_: *mut crate::leanh::LeanObject,
    mut v_x_3280_: *mut crate::leanh::LeanObject,
    mut v_x_3281_: usize,
    mut v_x_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3283_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___redArg(v_x_3280_, v_x_3281_, v_x_3282_);
    return v___x_3283_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1___boxed(
    mut v_00_u03b2_3284_: *mut crate::leanh::LeanObject,
    mut v_x_3285_: *mut crate::leanh::LeanObject,
    mut v_x_3286_: *mut crate::leanh::LeanObject,
    mut v_x_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8042__boxed_3288_: usize = 0;
    let mut v_res_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8042__boxed_3288_ = crate::leanh::lean_unbox_usize(v_x_3286_);
    crate::leanh::lean_dec(v_x_3286_);
    v_res_3289_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1(v_00_u03b2_3284_, v_x_3285_, v_x_8042__boxed_3288_, v_x_3287_);
    crate::leanh::lean_dec(v_x_3287_);
    crate::leanh::lean_dec_ref(v_x_3285_);
    return v_res_3289_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(
    mut v_00_u03b2_3290_: *mut crate::leanh::LeanObject,
    mut v_keys_3291_: *mut crate::leanh::LeanObject,
    mut v_vals_3292_: *mut crate::leanh::LeanObject,
    mut v_heq_3293_: *mut crate::leanh::LeanObject,
    mut v_i_3294_: *mut crate::leanh::LeanObject,
    mut v_k_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___redArg(v_keys_3291_, v_vals_3292_, v_i_3294_, v_k_3295_);
    return v___x_3296_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_3297_: *mut crate::leanh::LeanObject,
    mut v_keys_3298_: *mut crate::leanh::LeanObject,
    mut v_vals_3299_: *mut crate::leanh::LeanObject,
    mut v_heq_3300_: *mut crate::leanh::LeanObject,
    mut v_i_3301_: *mut crate::leanh::LeanObject,
    mut v_k_3302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3303_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__1_spec__1_spec__3(v_00_u03b2_3297_, v_keys_3298_, v_vals_3299_, v_heq_3300_, v_i_3301_, v_k_3302_);
    crate::leanh::lean_dec(v_k_3302_);
    crate::leanh::lean_dec_ref(v_vals_3299_);
    crate::leanh::lean_dec_ref(v_keys_3298_);
    return v_res_3303_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withInlining___redArg(
    mut v_value_3306_: *mut crate::leanh::LeanObject,
    mut v_recursive_3307_: u8,
    mut v_x_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStack_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStackOccs_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_value_3306_) == 3 {
                    v_declName_3317_ = crate::leanh::lean_ctor_get(v_value_3306_, 0);
                    crate::leanh::lean_inc_n(v_declName_3317_, 2);
                    crate::leanh::lean_dec_ref_known(v_value_3306_, 3);
                    v___x_3318_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_3307_, v_declName_3317_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                    if crate::leanh::lean_obj_tag(v___x_3318_) == 0 {
                        v_a_3319_ = crate::leanh::lean_ctor_get(v___x_3318_, 0);
                        crate::leanh::lean_inc(v_a_3319_);
                        crate::leanh::lean_dec_ref_known(v___x_3318_, 1);
                        v_declName_3320_ = crate::leanh::lean_ctor_get(v_a_3309_, 0);
                        v_config_3321_ = crate::leanh::lean_ctor_get(v_a_3309_, 1);
                        v_inlineStack_3322_ = crate::leanh::lean_ctor_get(v_a_3309_, 2);
                        v_inlineStackOccs_3323_ = crate::leanh::lean_ctor_get(v_a_3309_, 3);
                        v___x_3324_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0;
                        v___x_3325_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1;
                        crate::leanh::lean_inc(v_inlineStack_3322_);
                        crate::leanh::lean_inc(v_declName_3317_);
                        v___x_3326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3326_, 0, v_declName_3317_);
                        crate::leanh::lean_ctor_set(v___x_3326_, 1, v_inlineStack_3322_);
                        crate::leanh::lean_inc_ref(v_inlineStackOccs_3323_);
                        v___x_3327_ = l_Lean_PersistentHashMap_insert___redArg(
                            v___x_3324_,
                            v___x_3325_,
                            v_inlineStackOccs_3323_,
                            v_declName_3317_,
                            v_a_3319_,
                        );
                        crate::leanh::lean_inc_ref(v_config_3321_);
                        crate::leanh::lean_inc(v_declName_3320_);
                        v___x_3328_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3328_, 0, v_declName_3320_);
                        crate::leanh::lean_ctor_set(v___x_3328_, 1, v_config_3321_);
                        crate::leanh::lean_ctor_set(v___x_3328_, 2, v___x_3326_);
                        crate::leanh::lean_ctor_set(v___x_3328_, 3, v___x_3327_);
                        crate::leanh::lean_inc(v_a_3315_);
                        crate::leanh::lean_inc_ref(v_a_3314_);
                        crate::leanh::lean_inc(v_a_3313_);
                        crate::leanh::lean_inc_ref(v_a_3312_);
                        crate::leanh::lean_inc_ref(v_a_3311_);
                        crate::leanh::lean_inc(v_a_3310_);
                        v___x_3329_ = crate::leanh::lean_apply_8(
                            v_x_3308_,
                            v___x_3328_,
                            v_a_3310_,
                            v_a_3311_,
                            v_a_3312_,
                            v_a_3313_,
                            v_a_3314_,
                            v_a_3315_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3329_;
                    } else {
                        crate::leanh::lean_dec(v_declName_3317_);
                        crate::leanh::lean_dec_ref(v_x_3308_);
                        v_a_3330_ = crate::leanh::lean_ctor_get(v___x_3318_, 0);
                        v_isSharedCheck_3337_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3318_)) as u8;
                        if v_isSharedCheck_3337_ == 0 {
                            v___x_3332_ = v___x_3318_;
                            v_isShared_3333_ = v_isSharedCheck_3337_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3330_);
                            crate::leanh::lean_dec(v___x_3318_);
                            v___x_3332_ = crate::leanh::lean_box(0);
                            v_isShared_3333_ = v_isSharedCheck_3337_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3306_);
                    crate::leanh::lean_inc(v_a_3315_);
                    crate::leanh::lean_inc_ref(v_a_3314_);
                    crate::leanh::lean_inc(v_a_3313_);
                    crate::leanh::lean_inc_ref(v_a_3312_);
                    crate::leanh::lean_inc_ref(v_a_3311_);
                    crate::leanh::lean_inc(v_a_3310_);
                    crate::leanh::lean_inc_ref(v_a_3309_);
                    v___x_3338_ = crate::leanh::lean_apply_8(
                        v_x_3308_,
                        v_a_3309_,
                        v_a_3310_,
                        v_a_3311_,
                        v_a_3312_,
                        v_a_3313_,
                        v_a_3314_,
                        v_a_3315_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3338_;
                }
            }
            1 => {
                if v_isShared_3333_ == 0 {
                    v___x_3335_ = v___x_3332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
                    v___x_3335_ = v_reuseFailAlloc_3336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withInlining___redArg___boxed(
    mut v_value_3339_: *mut crate::leanh::LeanObject,
    mut v_recursive_3340_: *mut crate::leanh::LeanObject,
    mut v_x_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recursive_boxed_3350_: u8 = 0;
    let mut v_res_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_recursive_boxed_3350_ = (crate::leanh::lean_unbox(v_recursive_3340_) as u8);
    v_res_3351_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg(
        v_value_3339_,
        v_recursive_boxed_3350_,
        v_x_3341_,
        v_a_3342_,
        v_a_3343_,
        v_a_3344_,
        v_a_3345_,
        v_a_3346_,
        v_a_3347_,
        v_a_3348_,
    );
    crate::leanh::lean_dec(v_a_3348_);
    crate::leanh::lean_dec_ref(v_a_3347_);
    crate::leanh::lean_dec(v_a_3346_);
    crate::leanh::lean_dec_ref(v_a_3345_);
    crate::leanh::lean_dec_ref(v_a_3344_);
    crate::leanh::lean_dec(v_a_3343_);
    crate::leanh::lean_dec_ref(v_a_3342_);
    return v_res_3351_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withInlining(
    mut v_00_u03b1_3352_: *mut crate::leanh::LeanObject,
    mut v_value_3353_: *mut crate::leanh::LeanObject,
    mut v_recursive_3354_: u8,
    mut v_x_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStack_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStackOccs_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_value_3353_) == 3 {
                    v_declName_3364_ = crate::leanh::lean_ctor_get(v_value_3353_, 0);
                    crate::leanh::lean_inc_n(v_declName_3364_, 2);
                    crate::leanh::lean_dec_ref_known(v_value_3353_, 3);
                    v___x_3365_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_3354_, v_declName_3364_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
                    if crate::leanh::lean_obj_tag(v___x_3365_) == 0 {
                        v_a_3366_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                        crate::leanh::lean_inc(v_a_3366_);
                        crate::leanh::lean_dec_ref_known(v___x_3365_, 1);
                        v_declName_3367_ = crate::leanh::lean_ctor_get(v_a_3356_, 0);
                        v_config_3368_ = crate::leanh::lean_ctor_get(v_a_3356_, 1);
                        v_inlineStack_3369_ = crate::leanh::lean_ctor_get(v_a_3356_, 2);
                        v_inlineStackOccs_3370_ = crate::leanh::lean_ctor_get(v_a_3356_, 3);
                        v___x_3371_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__0;
                        v___x_3372_ = l_Lean_Compiler_LCNF_Simp_withInlining___redArg___closed__1;
                        crate::leanh::lean_inc(v_inlineStack_3369_);
                        crate::leanh::lean_inc(v_declName_3364_);
                        v___x_3373_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3373_, 0, v_declName_3364_);
                        crate::leanh::lean_ctor_set(v___x_3373_, 1, v_inlineStack_3369_);
                        crate::leanh::lean_inc_ref(v_inlineStackOccs_3370_);
                        v___x_3374_ = l_Lean_PersistentHashMap_insert___redArg(
                            v___x_3371_,
                            v___x_3372_,
                            v_inlineStackOccs_3370_,
                            v_declName_3364_,
                            v_a_3366_,
                        );
                        crate::leanh::lean_inc_ref(v_config_3368_);
                        crate::leanh::lean_inc(v_declName_3367_);
                        v___x_3375_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3375_, 0, v_declName_3367_);
                        crate::leanh::lean_ctor_set(v___x_3375_, 1, v_config_3368_);
                        crate::leanh::lean_ctor_set(v___x_3375_, 2, v___x_3373_);
                        crate::leanh::lean_ctor_set(v___x_3375_, 3, v___x_3374_);
                        crate::leanh::lean_inc(v_a_3362_);
                        crate::leanh::lean_inc_ref(v_a_3361_);
                        crate::leanh::lean_inc(v_a_3360_);
                        crate::leanh::lean_inc_ref(v_a_3359_);
                        crate::leanh::lean_inc_ref(v_a_3358_);
                        crate::leanh::lean_inc(v_a_3357_);
                        v___x_3376_ = crate::leanh::lean_apply_8(
                            v_x_3355_,
                            v___x_3375_,
                            v_a_3357_,
                            v_a_3358_,
                            v_a_3359_,
                            v_a_3360_,
                            v_a_3361_,
                            v_a_3362_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3376_;
                    } else {
                        crate::leanh::lean_dec(v_declName_3364_);
                        crate::leanh::lean_dec_ref(v_x_3355_);
                        v_a_3377_ = crate::leanh::lean_ctor_get(v___x_3365_, 0);
                        v_isSharedCheck_3384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3365_)) as u8;
                        if v_isSharedCheck_3384_ == 0 {
                            v___x_3379_ = v___x_3365_;
                            v_isShared_3380_ = v_isSharedCheck_3384_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3377_);
                            crate::leanh::lean_dec(v___x_3365_);
                            v___x_3379_ = crate::leanh::lean_box(0);
                            v_isShared_3380_ = v_isSharedCheck_3384_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3353_);
                    crate::leanh::lean_inc(v_a_3362_);
                    crate::leanh::lean_inc_ref(v_a_3361_);
                    crate::leanh::lean_inc(v_a_3360_);
                    crate::leanh::lean_inc_ref(v_a_3359_);
                    crate::leanh::lean_inc_ref(v_a_3358_);
                    crate::leanh::lean_inc(v_a_3357_);
                    crate::leanh::lean_inc_ref(v_a_3356_);
                    v___x_3385_ = crate::leanh::lean_apply_8(
                        v_x_3355_,
                        v_a_3356_,
                        v_a_3357_,
                        v_a_3358_,
                        v_a_3359_,
                        v_a_3360_,
                        v_a_3361_,
                        v_a_3362_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3385_;
                }
            }
            1 => {
                if v_isShared_3380_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withInlining___boxed(
    mut v_00_u03b1_3386_: *mut crate::leanh::LeanObject,
    mut v_value_3387_: *mut crate::leanh::LeanObject,
    mut v_recursive_3388_: *mut crate::leanh::LeanObject,
    mut v_x_3389_: *mut crate::leanh::LeanObject,
    mut v_a_3390_: *mut crate::leanh::LeanObject,
    mut v_a_3391_: *mut crate::leanh::LeanObject,
    mut v_a_3392_: *mut crate::leanh::LeanObject,
    mut v_a_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
    mut v_a_3397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recursive_boxed_3398_: u8 = 0;
    let mut v_res_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_recursive_boxed_3398_ = (crate::leanh::lean_unbox(v_recursive_3388_) as u8);
    v_res_3399_ = l_Lean_Compiler_LCNF_Simp_withInlining(
        v_00_u03b1_3386_,
        v_value_3387_,
        v_recursive_boxed_3398_,
        v_x_3389_,
        v_a_3390_,
        v_a_3391_,
        v_a_3392_,
        v_a_3393_,
        v_a_3394_,
        v_a_3395_,
        v_a_3396_,
    );
    crate::leanh::lean_dec(v_a_3396_);
    crate::leanh::lean_dec_ref(v_a_3395_);
    crate::leanh::lean_dec(v_a_3394_);
    crate::leanh::lean_dec_ref(v_a_3393_);
    crate::leanh::lean_dec_ref(v_a_3392_);
    crate::leanh::lean_dec(v_a_3391_);
    crate::leanh::lean_dec_ref(v_a_3390_);
    return v_res_3399_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__0;
    v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
    return v___x_3402_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3406_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__3;
    v___x_3407_ = l_Lean_MessageData_ofFormat(v___x_3406_);
    return v___x_3407_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(
    mut v_as_x27_3408_: *mut crate::leanh::LeanObject,
    mut v_b_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v_fst_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_unused_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3408_) == 0 {
                    v___x_3411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3411_, 0, v_b_3409_);
                    return v___x_3411_;
                } else {
                    v_snd_3412_ = crate::leanh::lean_ctor_get(v_b_3409_, 1);
                    crate::leanh::lean_inc(v_snd_3412_);
                    v_head_3413_ = crate::leanh::lean_ctor_get(v_as_x27_3408_, 0);
                    v_tail_3414_ = crate::leanh::lean_ctor_get(v_as_x27_3408_, 1);
                    v_fst_3415_ = crate::leanh::lean_ctor_get(v_b_3409_, 0);
                    v_isSharedCheck_3456_ = (!crate::leanh::lean_is_exclusive(v_b_3409_)) as u8;
                    if v_isSharedCheck_3456_ == 0 {
                        v_unused_3457_ = crate::leanh::lean_ctor_get(v_b_3409_, 1);
                        crate::leanh::lean_dec(v_unused_3457_);
                        v___x_3417_ = v_b_3409_;
                        v_isShared_3418_ = v_isSharedCheck_3456_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3415_);
                        crate::leanh::lean_dec(v_b_3409_);
                        v___x_3417_ = crate::leanh::lean_box(0);
                        v_isShared_3418_ = v_isSharedCheck_3456_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3419_ = crate::leanh::lean_ctor_get(v_snd_3412_, 0);
                v_snd_3420_ = crate::leanh::lean_ctor_get(v_snd_3412_, 1);
                v_isSharedCheck_3455_ = (!crate::leanh::lean_is_exclusive(v_snd_3412_)) as u8;
                if v_isSharedCheck_3455_ == 0 {
                    v___x_3422_ = v_snd_3412_;
                    v_isShared_3423_ = v_isSharedCheck_3455_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3420_);
                    crate::leanh::lean_inc(v_fst_3419_);
                    crate::leanh::lean_dec(v_snd_3412_);
                    v___x_3422_ = crate::leanh::lean_box(0);
                    v_isShared_3423_ = v_isSharedCheck_3455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3424_ = lean_name_eq(v_fst_3419_, v_head_3413_);
                if v___x_3424_ == 0 {
                    crate::leanh::lean_dec(v_snd_3420_);
                    crate::leanh::lean_dec(v_fst_3419_);
                    v___x_3425_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
                    crate::leanh::lean_inc_n(v_head_3413_, 2);
                    v___x_3426_ = l_Lean_MessageData_ofConstName(v_head_3413_, v___x_3424_);
                    v___x_3427_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3427_, 0, v___x_3426_);
                    crate::leanh::lean_ctor_set(v___x_3427_, 1, v___x_3425_);
                    v___x_3428_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3428_, 0, v_fst_3415_);
                    crate::leanh::lean_ctor_set(v___x_3428_, 1, v___x_3427_);
                    v___x_3429_ = crate::leanh::lean_box((v___x_3424_) as usize);
                    if v_isShared_3423_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3422_, 1, v___x_3429_);
                        crate::leanh::lean_ctor_set(v___x_3422_, 0, v_head_3413_);
                        v___x_3431_ = v___x_3422_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_head_3413_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3429_);
                        v___x_3431_ = v_reuseFailAlloc_3436_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3437_ = (crate::leanh::lean_unbox(v_snd_3420_) as u8);
                    if v___x_3437_ == 0 {
                        crate::leanh::lean_dec(v_snd_3420_);
                        v___x_3438_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__4);
                        v___x_3439_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3439_, 0, v_fst_3415_);
                        crate::leanh::lean_ctor_set(v___x_3439_, 1, v___x_3438_);
                        v___x_3440_ = crate::leanh::lean_box((v___x_3424_) as usize);
                        if v_isShared_3423_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3422_, 1, v___x_3440_);
                            v___x_3442_ = v___x_3422_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3447_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_fst_3419_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3440_);
                            v___x_3442_ = v_reuseFailAlloc_3447_;
                            state = 5;
                            continue;
                        }
                    } else {
                        if v_isShared_3423_ == 0 {
                            v___x_3449_ = v___x_3422_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3454_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_fst_3419_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_snd_3420_);
                            v___x_3449_ = v_reuseFailAlloc_3454_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_3418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3417_, 1, v___x_3431_);
                    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3428_);
                    v___x_3433_ = v___x_3417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 1, v___x_3431_);
                    v___x_3433_ = v_reuseFailAlloc_3435_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_as_x27_3408_ = v_tail_3414_;
                v_b_3409_ = v___x_3433_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3417_, 1, v___x_3442_);
                    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3439_);
                    v___x_3444_ = v___x_3417_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 1, v___x_3442_);
                    v___x_3444_ = v_reuseFailAlloc_3446_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_as_x27_3408_ = v_tail_3414_;
                v_b_3409_ = v___x_3444_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_3418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3417_, 1, v___x_3449_);
                    v___x_3451_ = v___x_3417_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_fst_3415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3449_);
                    v___x_3451_ = v_reuseFailAlloc_3453_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_as_x27_3408_ = v_tail_3414_;
                v_b_3409_ = v___x_3451_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___boxed(
    mut v_as_x27_3458_: *mut crate::leanh::LeanObject,
    mut v_b_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_3458_, v_b_3459_);
    crate::leanh::lean_dec(v_as_x27_3458_);
    return v_res_3461_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3462_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3463_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__0);
    v___x_3465_ = l_Lean_MessageData_ofFormat(v___x_3464_);
    return v___x_3465_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3467_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__2;
    v___x_3468_ = l_Lean_stringToMessageData(v___x_3467_);
    return v___x_3468_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(
    mut v_a_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_a_3473_: *mut crate::leanh::LeanObject,
    mut v_a_3474_: *mut crate::leanh::LeanObject,
    mut v_a_3475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inlineStack_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: u8 = 0;
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3494_: u8 = 0;
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3500_: u8 = 0;
    let mut v_unused_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inlineStack_3477_ = crate::leanh::lean_ctor_get(v_a_3469_, 2);
                if crate::leanh::lean_obj_tag(v_inlineStack_3477_) == 0 {
                    v___x_3478_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__1);
                    v___x_3479_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_3478_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
                    return v___x_3479_;
                } else {
                    v_head_3480_ = crate::leanh::lean_ctor_get(v_inlineStack_3477_, 0);
                    v_tail_3481_ = crate::leanh::lean_ctor_get(v_inlineStack_3477_, 1);
                    v___x_3482_ = 0;
                    crate::leanh::lean_inc_n(v_head_3480_, 2);
                    v___x_3483_ = l_Lean_MessageData_ofConstName(v_head_3480_, v___x_3482_);
                    v___x_3484_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg___closed__1);
                    v___x_3485_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3485_, 0, v___x_3483_);
                    crate::leanh::lean_ctor_set(v___x_3485_, 1, v___x_3484_);
                    v___x_3486_ = crate::leanh::lean_box((v___x_3482_) as usize);
                    v___x_3487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3487_, 0, v_head_3480_);
                    crate::leanh::lean_ctor_set(v___x_3487_, 1, v___x_3486_);
                    v___x_3488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3488_, 0, v___x_3485_);
                    crate::leanh::lean_ctor_set(v___x_3488_, 1, v___x_3487_);
                    v___x_3489_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_tail_3481_, v___x_3488_);
                    v_a_3490_ = crate::leanh::lean_ctor_get(v___x_3489_, 0);
                    crate::leanh::lean_inc(v_a_3490_);
                    crate::leanh::lean_dec_ref(v___x_3489_);
                    v_fst_3491_ = crate::leanh::lean_ctor_get(v_a_3490_, 0);
                    v_isSharedCheck_3500_ = (!crate::leanh::lean_is_exclusive(v_a_3490_)) as u8;
                    if v_isSharedCheck_3500_ == 0 {
                        v_unused_3501_ = crate::leanh::lean_ctor_get(v_a_3490_, 1);
                        crate::leanh::lean_dec(v_unused_3501_);
                        v___x_3493_ = v_a_3490_;
                        v_isShared_3494_ = v_isSharedCheck_3500_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3491_);
                        crate::leanh::lean_dec(v_a_3490_);
                        v___x_3493_ = crate::leanh::lean_box(0);
                        v_isShared_3494_ = v_isSharedCheck_3500_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3495_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___closed__3);
                if v_isShared_3494_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3493_, 7);
                    crate::leanh::lean_ctor_set(v___x_3493_, 1, v_fst_3491_);
                    crate::leanh::lean_ctor_set(v___x_3493_, 0, v___x_3495_);
                    v___x_3497_ = v___x_3493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3499_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_fst_3491_);
                    v___x_3497_ = v_reuseFailAlloc_3499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3498_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check_spec__0___redArg(v___x_3497_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
                return v___x_3498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg___boxed(
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
    mut v_a_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3510_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
    crate::leanh::lean_dec(v_a_3508_);
    crate::leanh::lean_dec_ref(v_a_3507_);
    crate::leanh::lean_dec(v_a_3506_);
    crate::leanh::lean_dec_ref(v_a_3505_);
    crate::leanh::lean_dec_ref(v_a_3504_);
    crate::leanh::lean_dec(v_a_3503_);
    crate::leanh::lean_dec_ref(v_a_3502_);
    return v_res_3510_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(
    mut v_00_u03b1_3511_: *mut crate::leanh::LeanObject,
    mut v_a_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
    return v___x_3520_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___boxed(
    mut v_00_u03b1_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3530_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(v_00_u03b1_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
    crate::leanh::lean_dec(v_a_3528_);
    crate::leanh::lean_dec_ref(v_a_3527_);
    crate::leanh::lean_dec(v_a_3526_);
    crate::leanh::lean_dec_ref(v_a_3525_);
    crate::leanh::lean_dec_ref(v_a_3524_);
    crate::leanh::lean_dec(v_a_3523_);
    crate::leanh::lean_dec_ref(v_a_3522_);
    return v_res_3530_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(
    mut v_as_3531_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3532_: *mut crate::leanh::LeanObject,
    mut v_b_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3543_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___redArg(v_as_x27_3532_, v_b_3533_);
    return v___x_3543_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0___boxed(
    mut v_as_3544_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3545_: *mut crate::leanh::LeanObject,
    mut v_b_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth_spec__0(v_as_3544_, v_as_x27_3545_, v_b_3546_, v_a_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
    crate::leanh::lean_dec(v___y_3554_);
    crate::leanh::lean_dec_ref(v___y_3553_);
    crate::leanh::lean_dec(v___y_3552_);
    crate::leanh::lean_dec_ref(v___y_3551_);
    crate::leanh::lean_dec_ref(v___y_3550_);
    crate::leanh::lean_dec(v___y_3549_);
    crate::leanh::lean_dec_ref(v___y_3548_);
    crate::leanh::lean_dec(v_as_x27_3545_);
    crate::leanh::lean_dec(v_as_3544_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(
    mut v_x_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
    mut v_a_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_a_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3578_: u8 = 0;
    let mut v_cancelTk_x3f_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3580_: u8 = 0;
    let mut v_inheritedTraceOptions_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3566_ = crate::leanh::lean_ctor_get(v_a_3563_, 0);
                v_fileMap_3567_ = crate::leanh::lean_ctor_get(v_a_3563_, 1);
                v_options_3568_ = crate::leanh::lean_ctor_get(v_a_3563_, 2);
                v_currRecDepth_3569_ = crate::leanh::lean_ctor_get(v_a_3563_, 3);
                v_maxRecDepth_3570_ = crate::leanh::lean_ctor_get(v_a_3563_, 4);
                v_ref_3571_ = crate::leanh::lean_ctor_get(v_a_3563_, 5);
                v_currNamespace_3572_ = crate::leanh::lean_ctor_get(v_a_3563_, 6);
                v_openDecls_3573_ = crate::leanh::lean_ctor_get(v_a_3563_, 7);
                v_initHeartbeats_3574_ = crate::leanh::lean_ctor_get(v_a_3563_, 8);
                v_maxHeartbeats_3575_ = crate::leanh::lean_ctor_get(v_a_3563_, 9);
                v_quotContext_3576_ = crate::leanh::lean_ctor_get(v_a_3563_, 10);
                v_currMacroScope_3577_ = crate::leanh::lean_ctor_get(v_a_3563_, 11);
                v_diag_3578_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3563_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3579_ = crate::leanh::lean_ctor_get(v_a_3563_, 12);
                v_suppressElabErrors_3580_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3563_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3581_ = crate::leanh::lean_ctor_get(v_a_3563_, 13);
                v___x_3587_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3588_ = lean_nat_dec_eq(v_maxRecDepth_3570_, v___x_3587_);
                if v___x_3588_ == 0 {
                    v___x_3589_ = lean_nat_dec_eq(v_currRecDepth_3569_, v_maxRecDepth_3570_);
                    if v___x_3589_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3557_);
                        v___x_3590_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
                        return v___x_3590_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3583_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3584_ = lean_nat_add(v_currRecDepth_3569_, v___x_3583_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3581_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3579_);
                crate::leanh::lean_inc(v_currMacroScope_3577_);
                crate::leanh::lean_inc(v_quotContext_3576_);
                crate::leanh::lean_inc(v_maxHeartbeats_3575_);
                crate::leanh::lean_inc(v_initHeartbeats_3574_);
                crate::leanh::lean_inc(v_openDecls_3573_);
                crate::leanh::lean_inc(v_currNamespace_3572_);
                crate::leanh::lean_inc(v_ref_3571_);
                crate::leanh::lean_inc(v_maxRecDepth_3570_);
                crate::leanh::lean_inc_ref(v_options_3568_);
                crate::leanh::lean_inc_ref(v_fileMap_3567_);
                crate::leanh::lean_inc_ref(v_fileName_3566_);
                v___x_3585_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3585_, 0, v_fileName_3566_);
                crate::leanh::lean_ctor_set(v___x_3585_, 1, v_fileMap_3567_);
                crate::leanh::lean_ctor_set(v___x_3585_, 2, v_options_3568_);
                crate::leanh::lean_ctor_set(v___x_3585_, 3, v___x_3584_);
                crate::leanh::lean_ctor_set(v___x_3585_, 4, v_maxRecDepth_3570_);
                crate::leanh::lean_ctor_set(v___x_3585_, 5, v_ref_3571_);
                crate::leanh::lean_ctor_set(v___x_3585_, 6, v_currNamespace_3572_);
                crate::leanh::lean_ctor_set(v___x_3585_, 7, v_openDecls_3573_);
                crate::leanh::lean_ctor_set(v___x_3585_, 8, v_initHeartbeats_3574_);
                crate::leanh::lean_ctor_set(v___x_3585_, 9, v_maxHeartbeats_3575_);
                crate::leanh::lean_ctor_set(v___x_3585_, 10, v_quotContext_3576_);
                crate::leanh::lean_ctor_set(v___x_3585_, 11, v_currMacroScope_3577_);
                crate::leanh::lean_ctor_set(v___x_3585_, 12, v_cancelTk_x3f_3579_);
                crate::leanh::lean_ctor_set(v___x_3585_, 13, v_inheritedTraceOptions_3581_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3585_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3578_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3585_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3580_,
                );
                crate::leanh::lean_inc(v_a_3564_);
                crate::leanh::lean_inc(v_a_3562_);
                crate::leanh::lean_inc_ref(v_a_3561_);
                crate::leanh::lean_inc_ref(v_a_3560_);
                crate::leanh::lean_inc(v_a_3559_);
                crate::leanh::lean_inc_ref(v_a_3558_);
                v___x_3586_ = crate::leanh::lean_apply_8(
                    v_x_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                    v_a_3561_,
                    v_a_3562_,
                    v___x_3585_,
                    v_a_3564_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg___boxed(
    mut v_x_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
    mut v_a_3598_: *mut crate::leanh::LeanObject,
    mut v_a_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth___redArg(
        v_x_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_,
    );
    crate::leanh::lean_dec(v_a_3598_);
    crate::leanh::lean_dec_ref(v_a_3597_);
    crate::leanh::lean_dec(v_a_3596_);
    crate::leanh::lean_dec_ref(v_a_3595_);
    crate::leanh::lean_dec_ref(v_a_3594_);
    crate::leanh::lean_dec(v_a_3593_);
    crate::leanh::lean_dec_ref(v_a_3592_);
    return v_res_3600_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withIncRecDepth(
    mut v_00_u03b1_3601_: *mut crate::leanh::LeanObject,
    mut v_x_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3623_: u8 = 0;
    let mut v_cancelTk_x3f_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3625_: u8 = 0;
    let mut v_inheritedTraceOptions_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: u8 = 0;
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3611_ = crate::leanh::lean_ctor_get(v_a_3608_, 0);
                v_fileMap_3612_ = crate::leanh::lean_ctor_get(v_a_3608_, 1);
                v_options_3613_ = crate::leanh::lean_ctor_get(v_a_3608_, 2);
                v_currRecDepth_3614_ = crate::leanh::lean_ctor_get(v_a_3608_, 3);
                v_maxRecDepth_3615_ = crate::leanh::lean_ctor_get(v_a_3608_, 4);
                v_ref_3616_ = crate::leanh::lean_ctor_get(v_a_3608_, 5);
                v_currNamespace_3617_ = crate::leanh::lean_ctor_get(v_a_3608_, 6);
                v_openDecls_3618_ = crate::leanh::lean_ctor_get(v_a_3608_, 7);
                v_initHeartbeats_3619_ = crate::leanh::lean_ctor_get(v_a_3608_, 8);
                v_maxHeartbeats_3620_ = crate::leanh::lean_ctor_get(v_a_3608_, 9);
                v_quotContext_3621_ = crate::leanh::lean_ctor_get(v_a_3608_, 10);
                v_currMacroScope_3622_ = crate::leanh::lean_ctor_get(v_a_3608_, 11);
                v_diag_3623_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3624_ = crate::leanh::lean_ctor_get(v_a_3608_, 12);
                v_suppressElabErrors_3625_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3626_ = crate::leanh::lean_ctor_get(v_a_3608_, 13);
                v___x_3632_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3633_ = lean_nat_dec_eq(v_maxRecDepth_3615_, v___x_3632_);
                if v___x_3633_ == 0 {
                    v___x_3634_ = lean_nat_dec_eq(v_currRecDepth_3614_, v_maxRecDepth_3615_);
                    if v___x_3634_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3602_);
                        v___x_3635_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___redArg(v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
                        return v___x_3635_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3628_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3629_ = lean_nat_add(v_currRecDepth_3614_, v___x_3628_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3626_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3624_);
                crate::leanh::lean_inc(v_currMacroScope_3622_);
                crate::leanh::lean_inc(v_quotContext_3621_);
                crate::leanh::lean_inc(v_maxHeartbeats_3620_);
                crate::leanh::lean_inc(v_initHeartbeats_3619_);
                crate::leanh::lean_inc(v_openDecls_3618_);
                crate::leanh::lean_inc(v_currNamespace_3617_);
                crate::leanh::lean_inc(v_ref_3616_);
                crate::leanh::lean_inc(v_maxRecDepth_3615_);
                crate::leanh::lean_inc_ref(v_options_3613_);
                crate::leanh::lean_inc_ref(v_fileMap_3612_);
                crate::leanh::lean_inc_ref(v_fileName_3611_);
                v___x_3630_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3630_, 0, v_fileName_3611_);
                crate::leanh::lean_ctor_set(v___x_3630_, 1, v_fileMap_3612_);
                crate::leanh::lean_ctor_set(v___x_3630_, 2, v_options_3613_);
                crate::leanh::lean_ctor_set(v___x_3630_, 3, v___x_3629_);
                crate::leanh::lean_ctor_set(v___x_3630_, 4, v_maxRecDepth_3615_);
                crate::leanh::lean_ctor_set(v___x_3630_, 5, v_ref_3616_);
                crate::leanh::lean_ctor_set(v___x_3630_, 6, v_currNamespace_3617_);
                crate::leanh::lean_ctor_set(v___x_3630_, 7, v_openDecls_3618_);
                crate::leanh::lean_ctor_set(v___x_3630_, 8, v_initHeartbeats_3619_);
                crate::leanh::lean_ctor_set(v___x_3630_, 9, v_maxHeartbeats_3620_);
                crate::leanh::lean_ctor_set(v___x_3630_, 10, v_quotContext_3621_);
                crate::leanh::lean_ctor_set(v___x_3630_, 11, v_currMacroScope_3622_);
                crate::leanh::lean_ctor_set(v___x_3630_, 12, v_cancelTk_x3f_3624_);
                crate::leanh::lean_ctor_set(v___x_3630_, 13, v_inheritedTraceOptions_3626_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3623_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3625_,
                );
                crate::leanh::lean_inc(v_a_3609_);
                crate::leanh::lean_inc(v_a_3607_);
                crate::leanh::lean_inc_ref(v_a_3606_);
                crate::leanh::lean_inc_ref(v_a_3605_);
                crate::leanh::lean_inc(v_a_3604_);
                crate::leanh::lean_inc_ref(v_a_3603_);
                v___x_3631_ = crate::leanh::lean_apply_8(
                    v_x_3602_,
                    v_a_3603_,
                    v_a_3604_,
                    v_a_3605_,
                    v_a_3606_,
                    v_a_3607_,
                    v___x_3630_,
                    v_a_3609_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withIncRecDepth___boxed(
    mut v_00_u03b1_3636_: *mut crate::leanh::LeanObject,
    mut v_x_3637_: *mut crate::leanh::LeanObject,
    mut v_a_3638_: *mut crate::leanh::LeanObject,
    mut v_a_3639_: *mut crate::leanh::LeanObject,
    mut v_a_3640_: *mut crate::leanh::LeanObject,
    mut v_a_3641_: *mut crate::leanh::LeanObject,
    mut v_a_3642_: *mut crate::leanh::LeanObject,
    mut v_a_3643_: *mut crate::leanh::LeanObject,
    mut v_a_3644_: *mut crate::leanh::LeanObject,
    mut v_a_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3646_ = l_Lean_Compiler_LCNF_Simp_withIncRecDepth(
        v_00_u03b1_3636_,
        v_x_3637_,
        v_a_3638_,
        v_a_3639_,
        v_a_3640_,
        v_a_3641_,
        v_a_3642_,
        v_a_3643_,
        v_a_3644_,
    );
    crate::leanh::lean_dec(v_a_3644_);
    crate::leanh::lean_dec_ref(v_a_3643_);
    crate::leanh::lean_dec(v_a_3642_);
    crate::leanh::lean_dec_ref(v_a_3641_);
    crate::leanh::lean_dec_ref(v_a_3640_);
    crate::leanh::lean_dec(v_a_3639_);
    crate::leanh::lean_dec_ref(v_a_3638_);
    return v_res_3646_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(
    mut v_a_3647_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3648_: *mut crate::leanh::LeanObject,
    mut v___x_3649_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_3657_: u8 = 0;
    let mut v_visited_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3652_ = lean_st_ref_take(v_a_3647_);
                v_subst_3653_ = crate::leanh::lean_ctor_get(v___x_3652_, 0);
                v_used_3654_ = crate::leanh::lean_ctor_get(v___x_3652_, 1);
                v_binderRenaming_3655_ = crate::leanh::lean_ctor_get(v___x_3652_, 2);
                v_funDeclInfoMap_3656_ = crate::leanh::lean_ctor_get(v___x_3652_, 3);
                v_simplified_3657_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3652_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_3658_ = crate::leanh::lean_ctor_get(v___x_3652_, 4);
                v_inline_3659_ = crate::leanh::lean_ctor_get(v___x_3652_, 5);
                v_inlineLocal_3660_ = crate::leanh::lean_ctor_get(v___x_3652_, 6);
                v_isSharedCheck_3671_ = (!crate::leanh::lean_is_exclusive(v___x_3652_)) as u8;
                if v_isSharedCheck_3671_ == 0 {
                    v___x_3662_ = v___x_3652_;
                    v_isShared_3663_ = v_isSharedCheck_3671_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_3660_);
                    crate::leanh::lean_inc(v_inline_3659_);
                    crate::leanh::lean_inc(v_visited_3658_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_3656_);
                    crate::leanh::lean_inc(v_binderRenaming_3655_);
                    crate::leanh::lean_inc(v_used_3654_);
                    crate::leanh::lean_inc(v_subst_3653_);
                    crate::leanh::lean_dec(v___x_3652_);
                    v___x_3662_ = crate::leanh::lean_box(0);
                    v_isShared_3663_ = v_isSharedCheck_3671_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3664_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(
                    v_funDeclInfoMap_3656_,
                    v_fvarId_3648_,
                    v___x_3649_,
                );
                if v_isShared_3663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3662_, 3, v___x_3664_);
                    v___x_3666_ = v___x_3662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_subst_3653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_used_3654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_binderRenaming_3655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 3, v___x_3664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_visited_3658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 5, v_inline_3659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_inlineLocal_3660_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3670_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_3657_,
                    );
                    v___x_3666_ = v_reuseFailAlloc_3670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3667_ = lean_st_ref_set(v_a_3647_, v___x_3666_);
                v___x_3668_ = crate::leanh::lean_box(0);
                v___x_3669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3669_, 0, v___x_3668_);
                return v___x_3669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0___boxed(
    mut v_a_3672_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3673_: *mut crate::leanh::LeanObject,
    mut v___x_3674_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3677_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(
        v_a_3672_,
        v_fvarId_3673_,
        v___x_3674_,
        v_a_x3f_3675_,
    );
    crate::leanh::lean_dec(v_a_x3f_3675_);
    crate::leanh::lean_dec(v_a_3672_);
    return v_res_3677_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v_x_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3679_) == 0 {
                    v___x_3680_ = crate::leanh::lean_box(0);
                    return v___x_3680_;
                } else {
                    v_key_3681_ = crate::leanh::lean_ctor_get(v_x_3679_, 0);
                    v_value_3682_ = crate::leanh::lean_ctor_get(v_x_3679_, 1);
                    v_tail_3683_ = crate::leanh::lean_ctor_get(v_x_3679_, 2);
                    v___x_3684_ = l_Lean_instBEqFVarId_beq(v_key_3681_, v_a_3678_);
                    if v___x_3684_ == 0 {
                        v_x_3679_ = v_tail_3683_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3682_);
                        v___x_3686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3686_, 0, v_value_3682_);
                        return v___x_3686_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg___boxed(
    mut v_a_3687_: *mut crate::leanh::LeanObject,
    mut v_x_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3689_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_3687_, v_x_3688_);
    crate::leanh::lean_dec(v_x_3688_);
    crate::leanh::lean_dec(v_a_3687_);
    return v_res_3689_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(
    mut v_m_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u64 = 0;
    let mut v___x_3695_: u64 = 0;
    let mut v___x_3696_: u64 = 0;
    let mut v_fold_3697_: u64 = 0;
    let mut v___x_3698_: u64 = 0;
    let mut v___x_3699_: u64 = 0;
    let mut v___x_3700_: u64 = 0;
    let mut v___x_3701_: usize = 0;
    let mut v___x_3702_: usize = 0;
    let mut v___x_3703_: usize = 0;
    let mut v___x_3704_: usize = 0;
    let mut v___x_3705_: usize = 0;
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3692_ = crate::leanh::lean_ctor_get(v_m_3690_, 1);
    v___x_3693_ = lean_array_get_size(v_buckets_3692_);
    v___x_3694_ = l_Lean_instHashableFVarId_hash(v_a_3691_);
    v___x_3695_ = 32u64;
    v___x_3696_ = lean_uint64_shift_right(v___x_3694_, v___x_3695_);
    v_fold_3697_ = lean_uint64_xor(v___x_3694_, v___x_3696_);
    v___x_3698_ = 16u64;
    v___x_3699_ = lean_uint64_shift_right(v_fold_3697_, v___x_3698_);
    v___x_3700_ = lean_uint64_xor(v_fold_3697_, v___x_3699_);
    v___x_3701_ = lean_uint64_to_usize(v___x_3700_);
    v___x_3702_ = lean_usize_of_nat(v___x_3693_);
    v___x_3703_ = 1usize;
    v___x_3704_ = lean_usize_sub(v___x_3702_, v___x_3703_);
    v___x_3705_ = lean_usize_land(v___x_3701_, v___x_3704_);
    v___x_3706_ = lean_array_uget_borrowed(v_buckets_3692_, v___x_3705_);
    v___x_3707_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_3691_, v___x_3706_);
    return v___x_3707_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg___boxed(
    mut v_m_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_3708_, v_a_3709_);
    crate::leanh::lean_dec(v_a_3709_);
    crate::leanh::lean_dec_ref(v_m_3708_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(
    mut v_fvarId_3711_: *mut crate::leanh::LeanObject,
    mut v_x_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_a_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3730_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3734_: u8 = 0;
    let mut v_unused_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_unused_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_a_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3721_ = lean_st_ref_get(v_a_3714_);
                v_funDeclInfoMap_3722_ = crate::leanh::lean_ctor_get(v___x_3721_, 3);
                crate::leanh::lean_inc_ref(v_funDeclInfoMap_3722_);
                crate::leanh::lean_dec(v___x_3721_);
                v___x_3723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_3722_, v_fvarId_3711_);
                crate::leanh::lean_dec_ref(v_funDeclInfoMap_3722_);
                crate::leanh::lean_inc(v_fvarId_3711_);
                v___x_3736_ =
                    l_Lean_Compiler_LCNF_Simp_addMustInline___redArg(v_fvarId_3711_, v_a_3714_);
                crate::leanh::lean_dec_ref(v___x_3736_);
                crate::leanh::lean_inc(v_a_3719_);
                crate::leanh::lean_inc_ref(v_a_3718_);
                crate::leanh::lean_inc(v_a_3717_);
                crate::leanh::lean_inc_ref(v_a_3716_);
                crate::leanh::lean_inc_ref(v_a_3715_);
                crate::leanh::lean_inc(v_a_3714_);
                crate::leanh::lean_inc_ref(v_a_3713_);
                v___x_3737_ = crate::leanh::lean_apply_8(
                    v_x_3712_,
                    v_a_3713_,
                    v_a_3714_,
                    v_a_3715_,
                    v_a_3716_,
                    v_a_3717_,
                    v_a_3718_,
                    v_a_3719_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3737_) == 0 {
                    v_a_3738_ = crate::leanh::lean_ctor_get(v___x_3737_, 0);
                    v_isSharedCheck_3754_ = (!crate::leanh::lean_is_exclusive(v___x_3737_)) as u8;
                    if v_isSharedCheck_3754_ == 0 {
                        v___x_3740_ = v___x_3737_;
                        v_isShared_3741_ = v_isSharedCheck_3754_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3738_);
                        crate::leanh::lean_dec(v___x_3737_);
                        v___x_3740_ = crate::leanh::lean_box(0);
                        v_isShared_3741_ = v_isSharedCheck_3754_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_3755_ = crate::leanh::lean_ctor_get(v___x_3737_, 0);
                    crate::leanh::lean_inc(v_a_3755_);
                    crate::leanh::lean_dec_ref_known(v___x_3737_, 1);
                    v_a_3725_ = v_a_3755_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3726_ = crate::leanh::lean_box(0);
                v___x_3727_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(
                    v_a_3714_,
                    v_fvarId_3711_,
                    v___x_3723_,
                    v___x_3726_,
                );
                v_isSharedCheck_3734_ = (!crate::leanh::lean_is_exclusive(v___x_3727_)) as u8;
                if v_isSharedCheck_3734_ == 0 {
                    v_unused_3735_ = crate::leanh::lean_ctor_get(v___x_3727_, 0);
                    crate::leanh::lean_dec(v_unused_3735_);
                    v___x_3729_ = v___x_3727_;
                    v_isShared_3730_ = v_isSharedCheck_3734_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3727_);
                    v___x_3729_ = crate::leanh::lean_box(0);
                    v_isShared_3730_ = v_isSharedCheck_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3730_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3729_, 1);
                    crate::leanh::lean_ctor_set(v___x_3729_, 0, v_a_3725_);
                    v___x_3732_ = v___x_3729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3725_);
                    v___x_3732_ = v_reuseFailAlloc_3733_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3732_;
            }
            4 => {
                crate::leanh::lean_inc(v_a_3738_);
                if v_isShared_3741_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3740_, 1);
                    v___x_3743_ = v___x_3740_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3738_);
                    v___x_3743_ = v_reuseFailAlloc_3753_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3744_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___lam__0(
                    v_a_3714_,
                    v_fvarId_3711_,
                    v___x_3723_,
                    v___x_3743_,
                );
                crate::leanh::lean_dec_ref(v___x_3743_);
                v_isSharedCheck_3751_ = (!crate::leanh::lean_is_exclusive(v___x_3744_)) as u8;
                if v_isSharedCheck_3751_ == 0 {
                    v_unused_3752_ = crate::leanh::lean_ctor_get(v___x_3744_, 0);
                    crate::leanh::lean_dec(v_unused_3752_);
                    v___x_3746_ = v___x_3744_;
                    v_isShared_3747_ = v_isSharedCheck_3751_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3744_);
                    v___x_3746_ = crate::leanh::lean_box(0);
                    v_isShared_3747_ = v_isSharedCheck_3751_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3747_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3746_, 0, v_a_3738_);
                    v___x_3749_ = v___x_3746_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3738_);
                    v___x_3749_ = v_reuseFailAlloc_3750_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg___boxed(
    mut v_fvarId_3756_: *mut crate::leanh::LeanObject,
    mut v_x_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
    mut v_a_3759_: *mut crate::leanh::LeanObject,
    mut v_a_3760_: *mut crate::leanh::LeanObject,
    mut v_a_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(
        v_fvarId_3756_,
        v_x_3757_,
        v_a_3758_,
        v_a_3759_,
        v_a_3760_,
        v_a_3761_,
        v_a_3762_,
        v_a_3763_,
        v_a_3764_,
    );
    crate::leanh::lean_dec(v_a_3764_);
    crate::leanh::lean_dec_ref(v_a_3763_);
    crate::leanh::lean_dec(v_a_3762_);
    crate::leanh::lean_dec_ref(v_a_3761_);
    crate::leanh::lean_dec_ref(v_a_3760_);
    crate::leanh::lean_dec(v_a_3759_);
    crate::leanh::lean_dec_ref(v_a_3758_);
    return v_res_3766_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withAddMustInline(
    mut v_00_u03b1_3767_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3768_: *mut crate::leanh::LeanObject,
    mut v_x_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_a_3771_: *mut crate::leanh::LeanObject,
    mut v_a_3772_: *mut crate::leanh::LeanObject,
    mut v_a_3773_: *mut crate::leanh::LeanObject,
    mut v_a_3774_: *mut crate::leanh::LeanObject,
    mut v_a_3775_: *mut crate::leanh::LeanObject,
    mut v_a_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3778_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline___redArg(
        v_fvarId_3768_,
        v_x_3769_,
        v_a_3770_,
        v_a_3771_,
        v_a_3772_,
        v_a_3773_,
        v_a_3774_,
        v_a_3775_,
        v_a_3776_,
    );
    return v___x_3778_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_withAddMustInline___boxed(
    mut v_00_u03b1_3779_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3780_: *mut crate::leanh::LeanObject,
    mut v_x_3781_: *mut crate::leanh::LeanObject,
    mut v_a_3782_: *mut crate::leanh::LeanObject,
    mut v_a_3783_: *mut crate::leanh::LeanObject,
    mut v_a_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
    mut v_a_3786_: *mut crate::leanh::LeanObject,
    mut v_a_3787_: *mut crate::leanh::LeanObject,
    mut v_a_3788_: *mut crate::leanh::LeanObject,
    mut v_a_3789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3790_ = l_Lean_Compiler_LCNF_Simp_withAddMustInline(
        v_00_u03b1_3779_,
        v_fvarId_3780_,
        v_x_3781_,
        v_a_3782_,
        v_a_3783_,
        v_a_3784_,
        v_a_3785_,
        v_a_3786_,
        v_a_3787_,
        v_a_3788_,
    );
    crate::leanh::lean_dec(v_a_3788_);
    crate::leanh::lean_dec_ref(v_a_3787_);
    crate::leanh::lean_dec(v_a_3786_);
    crate::leanh::lean_dec_ref(v_a_3785_);
    crate::leanh::lean_dec_ref(v_a_3784_);
    crate::leanh::lean_dec(v_a_3783_);
    crate::leanh::lean_dec_ref(v_a_3782_);
    return v_res_3790_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(
    mut v_00_u03b2_3791_: *mut crate::leanh::LeanObject,
    mut v_m_3792_: *mut crate::leanh::LeanObject,
    mut v_a_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_m_3792_, v_a_3793_);
    return v___x_3794_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___boxed(
    mut v_00_u03b2_3795_: *mut crate::leanh::LeanObject,
    mut v_m_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0(v_00_u03b2_3795_, v_m_3796_, v_a_3797_);
    crate::leanh::lean_dec(v_a_3797_);
    crate::leanh::lean_dec_ref(v_m_3796_);
    return v_res_3798_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(
    mut v_00_u03b2_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_x_3801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___redArg(v_a_3800_, v_x_3801_);
    return v___x_3802_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0___boxed(
    mut v_00_u03b2_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_x_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3806_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0_spec__0(v_00_u03b2_3803_, v_a_3804_, v_x_3805_);
    crate::leanh::lean_dec(v_x_3805_);
    crate::leanh::lean_dec(v_a_3804_);
    return v_res_3806_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(
    mut v_fvarId_3807_: *mut crate::leanh::LeanObject,
    mut v_a_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: u8 = 0;
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3818_ = lean_st_ref_get(v_a_3808_);
                v_funDeclInfoMap_3819_ = crate::leanh::lean_ctor_get(v___x_3818_, 3);
                crate::leanh::lean_inc_ref(v_funDeclInfoMap_3819_);
                crate::leanh::lean_dec(v___x_3818_);
                v___x_3820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_withAddMustInline_spec__0___redArg(v_funDeclInfoMap_3819_, v_fvarId_3807_);
                crate::leanh::lean_dec_ref(v_funDeclInfoMap_3819_);
                if crate::leanh::lean_obj_tag(v___x_3820_) == 1 {
                    v_val_3821_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                    crate::leanh::lean_inc(v_val_3821_);
                    crate::leanh::lean_dec_ref_known(v___x_3820_, 1);
                    v___x_3822_ = (crate::leanh::lean_unbox(v_val_3821_) as u8);
                    crate::leanh::lean_dec(v_val_3821_);
                    match v___x_3822_ {
                        0 => {
                            state = 2;
                            continue;
                        }
                        2 => {
                            state = 2;
                            continue;
                        }
                        _ => {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3820_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3811_ = 0;
                v___x_3812_ = crate::leanh::lean_box((v___x_3811_) as usize);
                v___x_3813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3813_, 0, v___x_3812_);
                return v___x_3813_;
            }
            2 => {
                v___x_3815_ = 1;
                v___x_3816_ = crate::leanh::lean_box((v___x_3815_) as usize);
                v___x_3817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3817_, 0, v___x_3816_);
                return v___x_3817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg___boxed(
    mut v_fvarId_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3826_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_3823_, v_a_3824_);
    crate::leanh::lean_dec(v_a_3824_);
    crate::leanh::lean_dec(v_fvarId_3823_);
    return v_res_3826_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(
    mut v_fvarId_3827_: *mut crate::leanh::LeanObject,
    mut v_a_3828_: *mut crate::leanh::LeanObject,
    mut v_a_3829_: *mut crate::leanh::LeanObject,
    mut v_a_3830_: *mut crate::leanh::LeanObject,
    mut v_a_3831_: *mut crate::leanh::LeanObject,
    mut v_a_3832_: *mut crate::leanh::LeanObject,
    mut v_a_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_3827_, v_a_3829_);
    return v___x_3836_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___boxed(
    mut v_fvarId_3837_: *mut crate::leanh::LeanObject,
    mut v_a_3838_: *mut crate::leanh::LeanObject,
    mut v_a_3839_: *mut crate::leanh::LeanObject,
    mut v_a_3840_: *mut crate::leanh::LeanObject,
    mut v_a_3841_: *mut crate::leanh::LeanObject,
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_a_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3846_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(
        v_fvarId_3837_,
        v_a_3838_,
        v_a_3839_,
        v_a_3840_,
        v_a_3841_,
        v_a_3842_,
        v_a_3843_,
        v_a_3844_,
    );
    crate::leanh::lean_dec(v_a_3844_);
    crate::leanh::lean_dec_ref(v_a_3843_);
    crate::leanh::lean_dec(v_a_3842_);
    crate::leanh::lean_dec_ref(v_a_3841_);
    crate::leanh::lean_dec_ref(v_a_3840_);
    crate::leanh::lean_dec(v_a_3839_);
    crate::leanh::lean_dec_ref(v_a_3838_);
    crate::leanh::lean_dec(v_fvarId_3837_);
    return v_res_3846_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isSmall___redArg(
    mut v_code_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v_smallThreshold_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: u8 = 0;
    let mut v___x_3857_: u8 = 0;
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_a_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3850_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_3848_);
                if crate::leanh::lean_obj_tag(v___x_3850_) == 0 {
                    v_a_3851_ = crate::leanh::lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3862_ = (!crate::leanh::lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3862_ == 0 {
                        v___x_3853_ = v___x_3850_;
                        v_isShared_3854_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3851_);
                        crate::leanh::lean_dec(v___x_3850_);
                        v___x_3853_ = crate::leanh::lean_box(0);
                        v_isShared_3854_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3863_ = crate::leanh::lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3870_ = (!crate::leanh::lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3870_ == 0 {
                        v___x_3865_ = v___x_3850_;
                        v_isShared_3866_ = v_isSharedCheck_3870_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3863_);
                        crate::leanh::lean_dec(v___x_3850_);
                        v___x_3865_ = crate::leanh::lean_box(0);
                        v_isShared_3866_ = v_isSharedCheck_3870_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_smallThreshold_3855_ = crate::leanh::lean_ctor_get(v_a_3851_, 0);
                crate::leanh::lean_inc(v_smallThreshold_3855_);
                crate::leanh::lean_dec(v_a_3851_);
                v___x_3856_ = 0;
                v___x_3857_ = l_Lean_Compiler_LCNF_Code_sizeLe(
                    v___x_3856_,
                    v_code_3847_,
                    v_smallThreshold_3855_,
                );
                crate::leanh::lean_dec(v_smallThreshold_3855_);
                v___x_3858_ = crate::leanh::lean_box((v___x_3857_) as usize);
                if v_isShared_3854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3853_, 0, v___x_3858_);
                    v___x_3860_ = v___x_3853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
                    v___x_3860_ = v_reuseFailAlloc_3861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3860_;
            }
            3 => {
                if v_isShared_3866_ == 0 {
                    v___x_3868_ = v___x_3865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isSmall___redArg___boxed(
    mut v_code_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3874_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_3871_, v_a_3872_);
    crate::leanh::lean_dec_ref(v_a_3872_);
    crate::leanh::lean_dec_ref(v_code_3871_);
    return v_res_3874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isSmall(
    mut v_code_3875_: *mut crate::leanh::LeanObject,
    mut v_a_3876_: *mut crate::leanh::LeanObject,
    mut v_a_3877_: *mut crate::leanh::LeanObject,
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_a_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
    mut v_a_3881_: *mut crate::leanh::LeanObject,
    mut v_a_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_code_3875_, v_a_3879_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isSmall___boxed(
    mut v_code_3885_: *mut crate::leanh::LeanObject,
    mut v_a_3886_: *mut crate::leanh::LeanObject,
    mut v_a_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
    mut v_a_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3894_ = l_Lean_Compiler_LCNF_Simp_isSmall(
        v_code_3885_,
        v_a_3886_,
        v_a_3887_,
        v_a_3888_,
        v_a_3889_,
        v_a_3890_,
        v_a_3891_,
        v_a_3892_,
    );
    crate::leanh::lean_dec(v_a_3892_);
    crate::leanh::lean_dec_ref(v_a_3891_);
    crate::leanh::lean_dec(v_a_3890_);
    crate::leanh::lean_dec_ref(v_a_3889_);
    crate::leanh::lean_dec_ref(v_a_3888_);
    crate::leanh::lean_dec(v_a_3887_);
    crate::leanh::lean_dec_ref(v_a_3886_);
    crate::leanh::lean_dec_ref(v_code_3885_);
    return v_res_3894_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(
    mut v_decl_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u8 = 0;
    v_fvarId_3899_ = crate::leanh::lean_ctor_get(v_decl_3895_, 0);
    v_value_3900_ = crate::leanh::lean_ctor_get(v_decl_3895_, 4);
    v___x_3901_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(v_fvarId_3899_, v_a_3896_);
    v_a_3902_ = crate::leanh::lean_ctor_get(v___x_3901_, 0);
    crate::leanh::lean_inc(v_a_3902_);
    v___x_3903_ = (crate::leanh::lean_unbox(v_a_3902_) as u8);
    crate::leanh::lean_dec(v_a_3902_);
    if v___x_3903_ == 0 {
        let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3901_);
        v___x_3904_ = l_Lean_Compiler_LCNF_Simp_isSmall___redArg(v_value_3900_, v_a_3897_);
        return v___x_3904_;
    } else {
        return v___x_3901_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg___boxed(
    mut v_decl_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
    mut v_a_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ =
        l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_3905_, v_a_3906_, v_a_3907_);
    crate::leanh::lean_dec_ref(v_a_3907_);
    crate::leanh::lean_dec(v_a_3906_);
    crate::leanh::lean_dec_ref(v_decl_3905_);
    return v_res_3909_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(
    mut v_decl_3910_: *mut crate::leanh::LeanObject,
    mut v_a_3911_: *mut crate::leanh::LeanObject,
    mut v_a_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
    mut v_a_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
    mut v_a_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ =
        l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(v_decl_3910_, v_a_3912_, v_a_3914_);
    return v___x_3919_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___boxed(
    mut v_decl_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
    mut v_a_3922_: *mut crate::leanh::LeanObject,
    mut v_a_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_a_3925_: *mut crate::leanh::LeanObject,
    mut v_a_3926_: *mut crate::leanh::LeanObject,
    mut v_a_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(
        v_decl_3920_,
        v_a_3921_,
        v_a_3922_,
        v_a_3923_,
        v_a_3924_,
        v_a_3925_,
        v_a_3926_,
        v_a_3927_,
    );
    crate::leanh::lean_dec(v_a_3927_);
    crate::leanh::lean_dec_ref(v_a_3926_);
    crate::leanh::lean_dec(v_a_3925_);
    crate::leanh::lean_dec_ref(v_a_3924_);
    crate::leanh::lean_dec_ref(v_a_3923_);
    crate::leanh::lean_dec(v_a_3922_);
    crate::leanh::lean_dec_ref(v_a_3921_);
    crate::leanh::lean_dec_ref(v_decl_3920_);
    return v_res_3929_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(
    mut v_a_3930_: *mut crate::leanh::LeanObject,
    mut v_b_3931_: *mut crate::leanh::LeanObject,
    mut v_x_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3932_) == 0 {
                    crate::leanh::lean_dec(v_b_3931_);
                    crate::leanh::lean_dec(v_a_3930_);
                    return v_x_3932_;
                } else {
                    v_key_3933_ = crate::leanh::lean_ctor_get(v_x_3932_, 0);
                    v_value_3934_ = crate::leanh::lean_ctor_get(v_x_3932_, 1);
                    v_tail_3935_ = crate::leanh::lean_ctor_get(v_x_3932_, 2);
                    v_isSharedCheck_3947_ = (!crate::leanh::lean_is_exclusive(v_x_3932_)) as u8;
                    if v_isSharedCheck_3947_ == 0 {
                        v___x_3937_ = v_x_3932_;
                        v_isShared_3938_ = v_isSharedCheck_3947_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3935_);
                        crate::leanh::lean_inc(v_value_3934_);
                        crate::leanh::lean_inc(v_key_3933_);
                        crate::leanh::lean_dec(v_x_3932_);
                        v___x_3937_ = crate::leanh::lean_box(0);
                        v_isShared_3938_ = v_isSharedCheck_3947_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3939_ = l_Lean_instBEqFVarId_beq(v_key_3933_, v_a_3930_);
                if v___x_3939_ == 0 {
                    v___x_3940_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_3930_, v_b_3931_, v_tail_3935_);
                    if v_isShared_3938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3937_, 2, v___x_3940_);
                        v___x_3942_ = v___x_3937_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3943_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_key_3933_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_value_3934_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 2, v___x_3940_);
                        v___x_3942_ = v_reuseFailAlloc_3943_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3934_);
                    crate::leanh::lean_dec(v_key_3933_);
                    if v_isShared_3938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3937_, 1, v_b_3931_);
                        crate::leanh::lean_ctor_set(v___x_3937_, 0, v_a_3930_);
                        v___x_3945_ = v___x_3937_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3946_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3930_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_b_3931_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_tail_3935_);
                        v___x_3945_ = v_reuseFailAlloc_3946_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3942_;
            }
            3 => {
                return v___x_3945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_x_3949_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3950_: u8 = 0;
    let mut v_key_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3949_) == 0 {
                    v___x_3950_ = 0;
                    return v___x_3950_;
                } else {
                    v_key_3951_ = crate::leanh::lean_ctor_get(v_x_3949_, 0);
                    v_tail_3952_ = crate::leanh::lean_ctor_get(v_x_3949_, 2);
                    v___x_3953_ = l_Lean_instBEqFVarId_beq(v_key_3951_, v_a_3948_);
                    if v___x_3953_ == 0 {
                        v_x_3949_ = v_tail_3952_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3953_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg___boxed(
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_x_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: u8 = 0;
    let mut v_r_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_3955_, v_x_3956_);
    crate::leanh::lean_dec(v_x_3956_);
    crate::leanh::lean_dec(v_a_3955_);
    v_r_3958_ = crate::leanh::lean_box((v_res_3957_) as usize);
    return v_r_3958_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_3959_: *mut crate::leanh::LeanObject,
    mut v_x_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u64 = 0;
    let mut v___x_3969_: u64 = 0;
    let mut v___x_3970_: u64 = 0;
    let mut v_fold_3971_: u64 = 0;
    let mut v___x_3972_: u64 = 0;
    let mut v___x_3973_: u64 = 0;
    let mut v___x_3974_: u64 = 0;
    let mut v___x_3975_: usize = 0;
    let mut v___x_3976_: usize = 0;
    let mut v___x_3977_: usize = 0;
    let mut v___x_3978_: usize = 0;
    let mut v___x_3979_: usize = 0;
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3960_) == 0 {
                    return v_x_3959_;
                } else {
                    v_key_3961_ = crate::leanh::lean_ctor_get(v_x_3960_, 0);
                    v_value_3962_ = crate::leanh::lean_ctor_get(v_x_3960_, 1);
                    v_tail_3963_ = crate::leanh::lean_ctor_get(v_x_3960_, 2);
                    v_isSharedCheck_3986_ = (!crate::leanh::lean_is_exclusive(v_x_3960_)) as u8;
                    if v_isSharedCheck_3986_ == 0 {
                        v___x_3965_ = v_x_3960_;
                        v_isShared_3966_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3963_);
                        crate::leanh::lean_inc(v_value_3962_);
                        crate::leanh::lean_inc(v_key_3961_);
                        crate::leanh::lean_dec(v_x_3960_);
                        v___x_3965_ = crate::leanh::lean_box(0);
                        v_isShared_3966_ = v_isSharedCheck_3986_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3967_ = lean_array_get_size(v_x_3959_);
                v___x_3968_ = l_Lean_instHashableFVarId_hash(v_key_3961_);
                v___x_3969_ = 32u64;
                v___x_3970_ = lean_uint64_shift_right(v___x_3968_, v___x_3969_);
                v_fold_3971_ = lean_uint64_xor(v___x_3968_, v___x_3970_);
                v___x_3972_ = 16u64;
                v___x_3973_ = lean_uint64_shift_right(v_fold_3971_, v___x_3972_);
                v___x_3974_ = lean_uint64_xor(v_fold_3971_, v___x_3973_);
                v___x_3975_ = lean_uint64_to_usize(v___x_3974_);
                v___x_3976_ = lean_usize_of_nat(v___x_3967_);
                v___x_3977_ = 1usize;
                v___x_3978_ = lean_usize_sub(v___x_3976_, v___x_3977_);
                v___x_3979_ = lean_usize_land(v___x_3975_, v___x_3978_);
                v___x_3980_ = lean_array_uget_borrowed(v_x_3959_, v___x_3979_);
                crate::leanh::lean_inc(v___x_3980_);
                if v_isShared_3966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3965_, 2, v___x_3980_);
                    v___x_3982_ = v___x_3965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_key_3961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_value_3962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 2, v___x_3980_);
                    v___x_3982_ = v_reuseFailAlloc_3985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3983_ = lean_array_uset(v_x_3959_, v___x_3979_, v___x_3982_);
                v_x_3959_ = v___x_3983_;
                v_x_3960_ = v_tail_3963_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(
    mut v_i_3987_: *mut crate::leanh::LeanObject,
    mut v_source_3988_: *mut crate::leanh::LeanObject,
    mut v_target_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v_es_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3990_ = lean_array_get_size(v_source_3988_);
                v___x_3991_ = lean_nat_dec_lt(v_i_3987_, v___x_3990_);
                if v___x_3991_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3988_);
                    crate::leanh::lean_dec(v_i_3987_);
                    return v_target_3989_;
                } else {
                    v_es_3992_ = lean_array_fget(v_source_3988_, v_i_3987_);
                    v___x_3993_ = crate::leanh::lean_box(0);
                    v_source_3994_ = lean_array_fset(v_source_3988_, v_i_3987_, v___x_3993_);
                    v_target_3995_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_target_3989_, v_es_3992_);
                    v___x_3996_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3997_ = lean_nat_add(v_i_3987_, v___x_3996_);
                    crate::leanh::lean_dec(v_i_3987_);
                    v_i_3987_ = v___x_3997_;
                    v_source_3988_ = v_source_3994_;
                    v_target_3989_ = v_target_3995_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(
    mut v_data_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = lean_array_get_size(v_data_3999_);
    v___x_4001_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4002_ = lean_nat_mul(v___x_4000_, v___x_4001_);
    v___x_4003_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4004_ = crate::leanh::lean_box(0);
    v___x_4005_ = lean_mk_array(v_nbuckets_4002_, v___x_4004_);
    v___x_4006_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v___x_4003_, v_data_3999_, v___x_4005_);
    return v___x_4006_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(
    mut v_m_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_b_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: u64 = 0;
    let mut v___x_4017_: u64 = 0;
    let mut v___x_4018_: u64 = 0;
    let mut v_fold_4019_: u64 = 0;
    let mut v___x_4020_: u64 = 0;
    let mut v___x_4021_: u64 = 0;
    let mut v___x_4022_: u64 = 0;
    let mut v___x_4023_: usize = 0;
    let mut v___x_4024_: usize = 0;
    let mut v___x_4025_: usize = 0;
    let mut v___x_4026_: usize = 0;
    let mut v___x_4027_: usize = 0;
    let mut v_bkt_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v_val_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4010_ = crate::leanh::lean_ctor_get(v_m_4007_, 0);
                v_buckets_4011_ = crate::leanh::lean_ctor_get(v_m_4007_, 1);
                v_isSharedCheck_4054_ = (!crate::leanh::lean_is_exclusive(v_m_4007_)) as u8;
                if v_isSharedCheck_4054_ == 0 {
                    v___x_4013_ = v_m_4007_;
                    v_isShared_4014_ = v_isSharedCheck_4054_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4011_);
                    crate::leanh::lean_inc(v_size_4010_);
                    crate::leanh::lean_dec(v_m_4007_);
                    v___x_4013_ = crate::leanh::lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4015_ = lean_array_get_size(v_buckets_4011_);
                v___x_4016_ = l_Lean_instHashableFVarId_hash(v_a_4008_);
                v___x_4017_ = 32u64;
                v___x_4018_ = lean_uint64_shift_right(v___x_4016_, v___x_4017_);
                v_fold_4019_ = lean_uint64_xor(v___x_4016_, v___x_4018_);
                v___x_4020_ = 16u64;
                v___x_4021_ = lean_uint64_shift_right(v_fold_4019_, v___x_4020_);
                v___x_4022_ = lean_uint64_xor(v_fold_4019_, v___x_4021_);
                v___x_4023_ = lean_uint64_to_usize(v___x_4022_);
                v___x_4024_ = lean_usize_of_nat(v___x_4015_);
                v___x_4025_ = 1usize;
                v___x_4026_ = lean_usize_sub(v___x_4024_, v___x_4025_);
                v___x_4027_ = lean_usize_land(v___x_4023_, v___x_4026_);
                v_bkt_4028_ = lean_array_uget_borrowed(v_buckets_4011_, v___x_4027_);
                v___x_4029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_4008_, v_bkt_4028_);
                if v___x_4029_ == 0 {
                    v___x_4030_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4031_ = lean_nat_add(v_size_4010_, v___x_4030_);
                    crate::leanh::lean_dec(v_size_4010_);
                    crate::leanh::lean_inc(v_bkt_4028_);
                    v___x_4032_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4032_, 0, v_a_4008_);
                    crate::leanh::lean_ctor_set(v___x_4032_, 1, v_b_4009_);
                    crate::leanh::lean_ctor_set(v___x_4032_, 2, v_bkt_4028_);
                    v_buckets_x27_4033_ =
                        lean_array_uset(v_buckets_4011_, v___x_4027_, v___x_4032_);
                    v___x_4034_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4035_ = lean_nat_mul(v_size_x27_4031_, v___x_4034_);
                    v___x_4036_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4037_ = lean_nat_div(v___x_4035_, v___x_4036_);
                    crate::leanh::lean_dec(v___x_4035_);
                    v___x_4038_ = lean_array_get_size(v_buckets_x27_4033_);
                    v___x_4039_ = lean_nat_dec_le(v___x_4037_, v___x_4038_);
                    crate::leanh::lean_dec(v___x_4037_);
                    if v___x_4039_ == 0 {
                        v_val_4040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_buckets_x27_4033_);
                        if v_isShared_4014_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4013_, 1, v_val_4040_);
                            crate::leanh::lean_ctor_set(v___x_4013_, 0, v_size_x27_4031_);
                            v___x_4042_ = v___x_4013_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4043_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4043_,
                                0,
                                v_size_x27_4031_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_val_4040_);
                            v___x_4042_ = v_reuseFailAlloc_4043_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4014_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4013_, 1, v_buckets_x27_4033_);
                            crate::leanh::lean_ctor_set(v___x_4013_, 0, v_size_x27_4031_);
                            v___x_4045_ = v___x_4013_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4046_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4046_,
                                0,
                                v_size_x27_4031_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4046_,
                                1,
                                v_buckets_x27_4033_,
                            );
                            v___x_4045_ = v_reuseFailAlloc_4046_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4028_);
                    v___x_4047_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4048_ =
                        lean_array_uset(v_buckets_4011_, v___x_4027_, v___x_4047_);
                    v___x_4049_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_4008_, v_b_4009_, v_bkt_4028_);
                    v___x_4050_ = lean_array_uset(v_buckets_x27_4048_, v___x_4027_, v___x_4049_);
                    if v_isShared_4014_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_4050_);
                        v___x_4052_ = v___x_4013_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_size_4010_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_4050_);
                        v___x_4052_ = v_reuseFailAlloc_4053_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4042_;
            }
            3 => {
                return v___x_4045_;
            }
            4 => {
                return v___x_4052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(
    mut v_as_4055_: *mut crate::leanh::LeanObject,
    mut v_sz_4056_: usize,
    mut v_i_4057_: usize,
    mut v_b_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v_array_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v_a_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: usize = 0;
    let mut v___x_4089_: usize = 0;
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_unused_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4060_ = lean_usize_dec_lt(v_i_4057_, v_sz_4056_);
                if v___x_4060_ == 0 {
                    v___x_4061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4061_, 0, v_b_4058_);
                    return v___x_4061_;
                } else {
                    v_snd_4062_ = crate::leanh::lean_ctor_get(v_b_4058_, 1);
                    v_fst_4063_ = crate::leanh::lean_ctor_get(v_b_4058_, 0);
                    v_isSharedCheck_4097_ = (!crate::leanh::lean_is_exclusive(v_b_4058_)) as u8;
                    if v_isSharedCheck_4097_ == 0 {
                        v___x_4065_ = v_b_4058_;
                        v_isShared_4066_ = v_isSharedCheck_4097_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4062_);
                        crate::leanh::lean_inc(v_fst_4063_);
                        crate::leanh::lean_dec(v_b_4058_);
                        v___x_4065_ = crate::leanh::lean_box(0);
                        v_isShared_4066_ = v_isSharedCheck_4097_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_4067_ = crate::leanh::lean_ctor_get(v_snd_4062_, 0);
                v_start_4068_ = crate::leanh::lean_ctor_get(v_snd_4062_, 1);
                v_stop_4069_ = crate::leanh::lean_ctor_get(v_snd_4062_, 2);
                v___x_4070_ = lean_nat_dec_lt(v_start_4068_, v_stop_4069_);
                if v___x_4070_ == 0 {
                    if v_isShared_4066_ == 0 {
                        v___x_4072_ = v___x_4065_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_fst_4063_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_snd_4062_);
                        v___x_4072_ = v_reuseFailAlloc_4074_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_4069_);
                    crate::leanh::lean_inc(v_start_4068_);
                    crate::leanh::lean_inc_ref(v_array_4067_);
                    v_isSharedCheck_4093_ = (!crate::leanh::lean_is_exclusive(v_snd_4062_)) as u8;
                    if v_isSharedCheck_4093_ == 0 {
                        v_unused_4094_ = crate::leanh::lean_ctor_get(v_snd_4062_, 2);
                        crate::leanh::lean_dec(v_unused_4094_);
                        v_unused_4095_ = crate::leanh::lean_ctor_get(v_snd_4062_, 1);
                        crate::leanh::lean_dec(v_unused_4095_);
                        v_unused_4096_ = crate::leanh::lean_ctor_get(v_snd_4062_, 0);
                        crate::leanh::lean_dec(v_unused_4096_);
                        v___x_4076_ = v_snd_4062_;
                        v_isShared_4077_ = v_isSharedCheck_4093_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_4062_);
                        v___x_4076_ = crate::leanh::lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4093_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
                return v___x_4073_;
            }
            3 => {
                v_a_4078_ = lean_array_uget_borrowed(v_as_4055_, v_i_4057_);
                v_fvarId_4079_ = crate::leanh::lean_ctor_get(v_a_4078_, 0);
                v___x_4080_ = lean_array_fget(v_array_4067_, v_start_4068_);
                v___x_4081_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4082_ = lean_nat_add(v_start_4068_, v___x_4081_);
                crate::leanh::lean_dec(v_start_4068_);
                if v_isShared_4077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4076_, 1, v___x_4082_);
                    v___x_4084_ = v___x_4076_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4092_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_array_4067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_stop_4069_);
                    v___x_4084_ = v_reuseFailAlloc_4092_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_fvarId_4079_);
                v___x_4085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_fst_4063_, v_fvarId_4079_, v___x_4080_);
                if v_isShared_4066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4065_, 1, v___x_4084_);
                    crate::leanh::lean_ctor_set(v___x_4065_, 0, v___x_4085_);
                    v___x_4087_ = v___x_4065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4084_);
                    v___x_4087_ = v_reuseFailAlloc_4091_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4088_ = 1usize;
                v___x_4089_ = lean_usize_add(v_i_4057_, v___x_4088_);
                v_i_4057_ = v___x_4089_;
                v_b_4058_ = v___x_4087_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg___boxed(
    mut v_as_4098_: *mut crate::leanh::LeanObject,
    mut v_sz_4099_: *mut crate::leanh::LeanObject,
    mut v_i_4100_: *mut crate::leanh::LeanObject,
    mut v_b_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4103_: usize = 0;
    let mut v_i_boxed_4104_: usize = 0;
    let mut v_res_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4103_ = crate::leanh::lean_unbox_usize(v_sz_4099_);
    crate::leanh::lean_dec(v_sz_4099_);
    v_i_boxed_4104_ = crate::leanh::lean_unbox_usize(v_i_4100_);
    crate::leanh::lean_dec(v_i_4100_);
    v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_4098_, v_sz_boxed_4103_, v_i_boxed_4104_, v_b_4101_);
    crate::leanh::lean_dec_ref(v_as_4098_);
    return v_res_4105_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_betaReduce(
    mut v_params_4106_: *mut crate::leanh::LeanObject,
    mut v_code_4107_: *mut crate::leanh::LeanObject,
    mut v_args_4108_: *mut crate::leanh::LeanObject,
    mut v_mustInline_4109_: u8,
    mut v_a_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
    mut v_a_4112_: *mut crate::leanh::LeanObject,
    mut v_a_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4123_: usize = 0;
    let mut v___x_4124_: usize = 0;
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: u8 = 0;
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4135_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_unused_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4118_ = crate::leanh::lean_unsigned_to_nat(0);
                v_subst_4119_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg___closed__1,
                );
                v___x_4120_ = lean_array_get_size(v_args_4108_);
                v___x_4121_ = l_Array_toSubarray___redArg(v_args_4108_, v___x_4118_, v___x_4120_);
                v___x_4122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4122_, 0, v_subst_4119_);
                crate::leanh::lean_ctor_set(v___x_4122_, 1, v___x_4121_);
                v_sz_4123_ = lean_array_size(v_params_4106_);
                v___x_4124_ = 0usize;
                v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_params_4106_, v_sz_4123_, v___x_4124_, v___x_4122_);
                if crate::leanh::lean_obj_tag(v___x_4125_) == 0 {
                    v_a_4126_ = crate::leanh::lean_ctor_get(v___x_4125_, 0);
                    crate::leanh::lean_inc(v_a_4126_);
                    crate::leanh::lean_dec_ref_known(v___x_4125_, 1);
                    v_fst_4127_ = crate::leanh::lean_ctor_get(v_a_4126_, 0);
                    crate::leanh::lean_inc(v_fst_4127_);
                    crate::leanh::lean_dec(v_a_4126_);
                    v___x_4128_ = 0;
                    v___x_4129_ = 0;
                    v___x_4130_ = l_Lean_Compiler_LCNF_Code_internalize(
                        v___x_4128_,
                        v_code_4107_,
                        v_fst_4127_,
                        v___x_4129_,
                        v_a_4113_,
                        v_a_4114_,
                        v_a_4115_,
                        v_a_4116_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4130_) == 0 {
                        v_a_4131_ = crate::leanh::lean_ctor_get(v___x_4130_, 0);
                        crate::leanh::lean_inc_n(v_a_4131_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4130_, 1);
                        v___x_4132_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
                            v_a_4131_,
                            v_mustInline_4109_,
                            v_a_4111_,
                            v_a_4113_,
                            v_a_4114_,
                            v_a_4115_,
                            v_a_4116_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4132_) == 0 {
                            v_isSharedCheck_4139_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4132_)) as u8;
                            if v_isSharedCheck_4139_ == 0 {
                                v_unused_4140_ = crate::leanh::lean_ctor_get(v___x_4132_, 0);
                                crate::leanh::lean_dec(v_unused_4140_);
                                v___x_4134_ = v___x_4132_;
                                v_isShared_4135_ = v_isSharedCheck_4139_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4132_);
                                v___x_4134_ = crate::leanh::lean_box(0);
                                v_isShared_4135_ = v_isSharedCheck_4139_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4131_);
                            v_a_4141_ = crate::leanh::lean_ctor_get(v___x_4132_, 0);
                            v_isSharedCheck_4148_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4132_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4143_ = v___x_4132_;
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4141_);
                                crate::leanh::lean_dec(v___x_4132_);
                                v___x_4143_ = crate::leanh::lean_box(0);
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        return v___x_4130_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_code_4107_);
                    v_a_4149_ = crate::leanh::lean_ctor_get(v___x_4125_, 0);
                    v_isSharedCheck_4156_ = (!crate::leanh::lean_is_exclusive(v___x_4125_)) as u8;
                    if v_isSharedCheck_4156_ == 0 {
                        v___x_4151_ = v___x_4125_;
                        v_isShared_4152_ = v_isSharedCheck_4156_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4149_);
                        crate::leanh::lean_dec(v___x_4125_);
                        v___x_4151_ = crate::leanh::lean_box(0);
                        v_isShared_4152_ = v_isSharedCheck_4156_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4135_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4134_, 0, v_a_4131_);
                    v___x_4137_ = v___x_4134_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4131_);
                    v___x_4137_ = v_reuseFailAlloc_4138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4137_;
            }
            3 => {
                if v_isShared_4144_ == 0 {
                    v___x_4146_ = v___x_4143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4146_;
            }
            5 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_betaReduce___boxed(
    mut v_params_4157_: *mut crate::leanh::LeanObject,
    mut v_code_4158_: *mut crate::leanh::LeanObject,
    mut v_args_4159_: *mut crate::leanh::LeanObject,
    mut v_mustInline_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mustInline_boxed_4169_: u8 = 0;
    let mut v_res_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mustInline_boxed_4169_ = (crate::leanh::lean_unbox(v_mustInline_4160_) as u8);
    v_res_4170_ = l_Lean_Compiler_LCNF_Simp_betaReduce(
        v_params_4157_,
        v_code_4158_,
        v_args_4159_,
        v_mustInline_boxed_4169_,
        v_a_4161_,
        v_a_4162_,
        v_a_4163_,
        v_a_4164_,
        v_a_4165_,
        v_a_4166_,
        v_a_4167_,
    );
    crate::leanh::lean_dec(v_a_4167_);
    crate::leanh::lean_dec_ref(v_a_4166_);
    crate::leanh::lean_dec(v_a_4165_);
    crate::leanh::lean_dec_ref(v_a_4164_);
    crate::leanh::lean_dec_ref(v_a_4163_);
    crate::leanh::lean_dec(v_a_4162_);
    crate::leanh::lean_dec_ref(v_a_4161_);
    crate::leanh::lean_dec_ref(v_params_4157_);
    return v_res_4170_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0(
    mut v_00_u03b2_4171_: *mut crate::leanh::LeanObject,
    mut v_m_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
    mut v_b_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4175_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_m_4172_, v_a_4173_, v_b_4174_);
    return v___x_4175_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(
    mut v_as_4176_: *mut crate::leanh::LeanObject,
    mut v_sz_4177_: usize,
    mut v_i_4178_: usize,
    mut v_b_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___redArg(v_as_4176_, v_sz_4177_, v_i_4178_, v_b_4179_);
    return v___x_4188_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1___boxed(
    mut v_as_4189_: *mut crate::leanh::LeanObject,
    mut v_sz_4190_: *mut crate::leanh::LeanObject,
    mut v_i_4191_: *mut crate::leanh::LeanObject,
    mut v_b_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4201_: usize = 0;
    let mut v_i_boxed_4202_: usize = 0;
    let mut v_res_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4201_ = crate::leanh::lean_unbox_usize(v_sz_4190_);
    crate::leanh::lean_dec(v_sz_4190_);
    v_i_boxed_4202_ = crate::leanh::lean_unbox_usize(v_i_4191_);
    crate::leanh::lean_dec(v_i_4191_);
    v_res_4203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__1(v_as_4189_, v_sz_boxed_4201_, v_i_boxed_4202_, v_b_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
    crate::leanh::lean_dec(v___y_4199_);
    crate::leanh::lean_dec_ref(v___y_4198_);
    crate::leanh::lean_dec(v___y_4197_);
    crate::leanh::lean_dec_ref(v___y_4196_);
    crate::leanh::lean_dec_ref(v___y_4195_);
    crate::leanh::lean_dec(v___y_4194_);
    crate::leanh::lean_dec_ref(v___y_4193_);
    crate::leanh::lean_dec_ref(v_as_4189_);
    return v_res_4203_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(
    mut v_00_u03b2_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
    mut v_x_4206_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4207_: u8 = 0;
    v___x_4207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___redArg(v_a_4205_, v_x_4206_);
    return v___x_4207_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0___boxed(
    mut v_00_u03b2_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_x_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4211_: u8 = 0;
    let mut v_r_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__0(v_00_u03b2_4208_, v_a_4209_, v_x_4210_);
    crate::leanh::lean_dec(v_x_4210_);
    crate::leanh::lean_dec(v_a_4209_);
    v_r_4212_ = crate::leanh::lean_box((v_res_4211_) as usize);
    return v_r_4212_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1(
    mut v_00_u03b2_4213_: *mut crate::leanh::LeanObject,
    mut v_data_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1___redArg(v_data_4214_);
    return v___x_4215_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2(
    mut v_00_u03b2_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_b_4218_: *mut crate::leanh::LeanObject,
    mut v_x_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__2___redArg(v_a_4217_, v_b_4218_, v_x_4219_);
    return v___x_4220_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4221_: *mut crate::leanh::LeanObject,
    mut v_i_4222_: *mut crate::leanh::LeanObject,
    mut v_source_4223_: *mut crate::leanh::LeanObject,
    mut v_target_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4225_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2___redArg(v_i_4222_, v_source_4223_, v_target_4224_);
    return v___x_4225_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4226_: *mut crate::leanh::LeanObject,
    mut v_x_4227_: *mut crate::leanh::LeanObject,
    mut v_x_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4227_, v_x_4228_);
    return v___x_4229_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
    mut v_decl_4230_: *mut crate::leanh::LeanObject,
    mut v_a_4231_: *mut crate::leanh::LeanObject,
    mut v_a_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4234_ = 0;
    v___x_4235_ = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(v___x_4234_, v_decl_4230_, v_a_4232_);
    if crate::leanh::lean_obj_tag(v___x_4235_) == 0 {
        let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_4235_, 1);
        v___x_4236_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_4231_);
        return v___x_4236_;
    } else {
        return v___x_4235_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg___boxed(
    mut v_decl_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
    mut v_a_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4241_ =
        l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_4237_, v_a_4238_, v_a_4239_);
    crate::leanh::lean_dec(v_a_4239_);
    crate::leanh::lean_dec(v_a_4238_);
    crate::leanh::lean_dec_ref(v_decl_4237_);
    return v_res_4241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseLetDecl(
    mut v_decl_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ =
        l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v_decl_4242_, v_a_4244_, v_a_4247_);
    return v___x_4251_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseLetDecl___boxed(
    mut v_decl_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
    mut v_a_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4261_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(
        v_decl_4252_,
        v_a_4253_,
        v_a_4254_,
        v_a_4255_,
        v_a_4256_,
        v_a_4257_,
        v_a_4258_,
        v_a_4259_,
    );
    crate::leanh::lean_dec(v_a_4259_);
    crate::leanh::lean_dec_ref(v_a_4258_);
    crate::leanh::lean_dec(v_a_4257_);
    crate::leanh::lean_dec_ref(v_a_4256_);
    crate::leanh::lean_dec_ref(v_a_4255_);
    crate::leanh::lean_dec(v_a_4254_);
    crate::leanh::lean_dec_ref(v_a_4253_);
    crate::leanh::lean_dec_ref(v_decl_4252_);
    return v_res_4261_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(
    mut v_decl_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4266_: u8 = 0;
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4266_ = 0;
    v___x_4267_ = 1;
    v___x_4268_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(
        v___x_4266_,
        v_decl_4262_,
        v___x_4267_,
        v_a_4264_,
    );
    if crate::leanh::lean_obj_tag(v___x_4268_) == 0 {
        let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_4268_, 1);
        v___x_4269_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_4263_);
        return v___x_4269_;
    } else {
        return v___x_4268_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg___boxed(
    mut v_decl_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4274_ =
        l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_4270_, v_a_4271_, v_a_4272_);
    crate::leanh::lean_dec(v_a_4272_);
    crate::leanh::lean_dec(v_a_4271_);
    crate::leanh::lean_dec_ref(v_decl_4270_);
    return v_res_4274_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseFunDecl(
    mut v_decl_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
    mut v_a_4278_: *mut crate::leanh::LeanObject,
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_a_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ =
        l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(v_decl_4275_, v_a_4277_, v_a_4280_);
    return v___x_4284_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_eraseFunDecl___boxed(
    mut v_decl_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
    mut v_a_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4294_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(
        v_decl_4285_,
        v_a_4286_,
        v_a_4287_,
        v_a_4288_,
        v_a_4289_,
        v_a_4290_,
        v_a_4291_,
        v_a_4292_,
    );
    crate::leanh::lean_dec(v_a_4292_);
    crate::leanh::lean_dec_ref(v_a_4291_);
    crate::leanh::lean_dec(v_a_4290_);
    crate::leanh::lean_dec_ref(v_a_4289_);
    crate::leanh::lean_dec_ref(v_a_4288_);
    crate::leanh::lean_dec(v_a_4287_);
    crate::leanh::lean_dec_ref(v_a_4286_);
    crate::leanh::lean_dec_ref(v_decl_4285_);
    return v_res_4294_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
    mut v_fvarId_4295_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_4296_: *mut crate::leanh::LeanObject,
    mut v_a_4297_: *mut crate::leanh::LeanObject,
    mut v_a_4298_: *mut crate::leanh::LeanObject,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_4308_: u8 = 0;
    let mut v_visited_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_4341_: u8 = 0;
    let mut v_visited_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4357_: u8 = 0;
    let mut v_isSharedCheck_4358_: u8 = 0;
    let mut v_a_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_reuseFailAlloc_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4303_ = lean_st_ref_take(v_a_4297_);
                v_subst_4304_ = crate::leanh::lean_ctor_get(v___x_4303_, 0);
                v_used_4305_ = crate::leanh::lean_ctor_get(v___x_4303_, 1);
                v_binderRenaming_4306_ = crate::leanh::lean_ctor_get(v___x_4303_, 2);
                v_funDeclInfoMap_4307_ = crate::leanh::lean_ctor_get(v___x_4303_, 3);
                v_simplified_4308_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4303_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_4309_ = crate::leanh::lean_ctor_get(v___x_4303_, 4);
                v_inline_4310_ = crate::leanh::lean_ctor_get(v___x_4303_, 5);
                v_inlineLocal_4311_ = crate::leanh::lean_ctor_get(v___x_4303_, 6);
                v_isSharedCheck_4381_ = (!crate::leanh::lean_is_exclusive(v___x_4303_)) as u8;
                if v_isSharedCheck_4381_ == 0 {
                    v___x_4313_ = v___x_4303_;
                    v_isShared_4314_ = v_isSharedCheck_4381_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_4311_);
                    crate::leanh::lean_inc(v_inline_4310_);
                    crate::leanh::lean_inc(v_visited_4309_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_4307_);
                    crate::leanh::lean_inc(v_binderRenaming_4306_);
                    crate::leanh::lean_inc(v_used_4305_);
                    crate::leanh::lean_inc(v_subst_4304_);
                    crate::leanh::lean_dec(v___x_4303_);
                    v___x_4313_ = crate::leanh::lean_box(0);
                    v_isShared_4314_ = v_isSharedCheck_4381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fvarId_x27_4296_);
                v___x_4315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4315_, 0, v_fvarId_x27_4296_);
                crate::leanh::lean_inc(v_fvarId_4295_);
                v___x_4316_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_betaReduce_spec__0___redArg(v_subst_4304_, v_fvarId_4295_, v___x_4315_);
                if v_isShared_4314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4313_, 0, v___x_4316_);
                    v___x_4318_ = v___x_4313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_used_4305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 2, v_binderRenaming_4306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 3, v_funDeclInfoMap_4307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 4, v_visited_4309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 5, v_inline_4310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 6, v_inlineLocal_4311_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4380_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_4308_,
                    );
                    v___x_4318_ = v_reuseFailAlloc_4380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4319_ = lean_st_ref_set(v_a_4297_, v___x_4318_);
                v___x_4320_ = l_Lean_Compiler_LCNF_getBinderName(
                    v_fvarId_4295_,
                    v_a_4298_,
                    v_a_4299_,
                    v_a_4300_,
                    v_a_4301_,
                );
                if crate::leanh::lean_obj_tag(v___x_4320_) == 0 {
                    v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                    v_isSharedCheck_4371_ = (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                    if v_isSharedCheck_4371_ == 0 {
                        v___x_4323_ = v___x_4320_;
                        v_isShared_4324_ = v_isSharedCheck_4371_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4321_);
                        crate::leanh::lean_dec(v___x_4320_);
                        v___x_4323_ = crate::leanh::lean_box(0);
                        v_isShared_4324_ = v_isSharedCheck_4371_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_x27_4296_);
                    v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                    v_isSharedCheck_4379_ = (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                    if v_isSharedCheck_4379_ == 0 {
                        v___x_4374_ = v___x_4320_;
                        v_isShared_4375_ = v_isSharedCheck_4379_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4372_);
                        crate::leanh::lean_dec(v___x_4320_);
                        v___x_4374_ = crate::leanh::lean_box(0);
                        v_isShared_4375_ = v_isSharedCheck_4379_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4325_ = l_Lean_Name_isInternal(v_a_4321_);
                if v___x_4325_ == 0 {
                    crate::leanh::lean_del_object(v___x_4323_);
                    crate::leanh::lean_inc(v_fvarId_x27_4296_);
                    v___x_4326_ = l_Lean_Compiler_LCNF_getBinderName(
                        v_fvarId_x27_4296_,
                        v_a_4298_,
                        v_a_4299_,
                        v_a_4300_,
                        v_a_4301_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4326_) == 0 {
                        v_a_4327_ = crate::leanh::lean_ctor_get(v___x_4326_, 0);
                        v_isSharedCheck_4358_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4326_)) as u8;
                        if v_isSharedCheck_4358_ == 0 {
                            v___x_4329_ = v___x_4326_;
                            v_isShared_4330_ = v_isSharedCheck_4358_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4327_);
                            crate::leanh::lean_dec(v___x_4326_);
                            v___x_4329_ = crate::leanh::lean_box(0);
                            v_isShared_4330_ = v_isSharedCheck_4358_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4321_);
                        crate::leanh::lean_dec(v_fvarId_x27_4296_);
                        v_a_4359_ = crate::leanh::lean_ctor_get(v___x_4326_, 0);
                        v_isSharedCheck_4366_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4326_)) as u8;
                        if v_isSharedCheck_4366_ == 0 {
                            v___x_4361_ = v___x_4326_;
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4359_);
                            crate::leanh::lean_dec(v___x_4326_);
                            v___x_4361_ = crate::leanh::lean_box(0);
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4321_);
                    crate::leanh::lean_dec(v_fvarId_x27_4296_);
                    v___x_4367_ = crate::leanh::lean_box(0);
                    if v_isShared_4324_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4367_);
                        v___x_4369_ = v___x_4323_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
                        v___x_4369_ = v_reuseFailAlloc_4370_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4331_ = l_Lean_Name_isInternal(v_a_4327_);
                crate::leanh::lean_dec(v_a_4327_);
                if v___x_4331_ == 0 {
                    crate::leanh::lean_dec(v_a_4321_);
                    crate::leanh::lean_dec(v_fvarId_x27_4296_);
                    v___x_4332_ = crate::leanh::lean_box(0);
                    if v_isShared_4330_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4329_, 0, v___x_4332_);
                        v___x_4334_ = v___x_4329_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4335_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
                        v___x_4334_ = v_reuseFailAlloc_4335_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_4336_ = lean_st_ref_take(v_a_4297_);
                    v_subst_4337_ = crate::leanh::lean_ctor_get(v___x_4336_, 0);
                    v_used_4338_ = crate::leanh::lean_ctor_get(v___x_4336_, 1);
                    v_binderRenaming_4339_ = crate::leanh::lean_ctor_get(v___x_4336_, 2);
                    v_funDeclInfoMap_4340_ = crate::leanh::lean_ctor_get(v___x_4336_, 3);
                    v_simplified_4341_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_4336_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    v_visited_4342_ = crate::leanh::lean_ctor_get(v___x_4336_, 4);
                    v_inline_4343_ = crate::leanh::lean_ctor_get(v___x_4336_, 5);
                    v_inlineLocal_4344_ = crate::leanh::lean_ctor_get(v___x_4336_, 6);
                    v_isSharedCheck_4357_ = (!crate::leanh::lean_is_exclusive(v___x_4336_)) as u8;
                    if v_isSharedCheck_4357_ == 0 {
                        v___x_4346_ = v___x_4336_;
                        v_isShared_4347_ = v_isSharedCheck_4357_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_inlineLocal_4344_);
                        crate::leanh::lean_inc(v_inline_4343_);
                        crate::leanh::lean_inc(v_visited_4342_);
                        crate::leanh::lean_inc(v_funDeclInfoMap_4340_);
                        crate::leanh::lean_inc(v_binderRenaming_4339_);
                        crate::leanh::lean_inc(v_used_4338_);
                        crate::leanh::lean_inc(v_subst_4337_);
                        crate::leanh::lean_dec(v___x_4336_);
                        v___x_4346_ = crate::leanh::lean_box(0);
                        v_isShared_4347_ = v_isSharedCheck_4357_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4334_;
            }
            6 => {
                v___x_4348_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_x27_4296_, v_a_4321_, v_binderRenaming_4339_);
                if v_isShared_4347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4346_, 2, v___x_4348_);
                    v___x_4350_ = v___x_4346_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4356_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_subst_4337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_used_4338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 2, v___x_4348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_funDeclInfoMap_4340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 4, v_visited_4342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 5, v_inline_4343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 6, v_inlineLocal_4344_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4356_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_4341_,
                    );
                    v___x_4350_ = v_reuseFailAlloc_4356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4351_ = lean_st_ref_set(v_a_4297_, v___x_4350_);
                v___x_4352_ = crate::leanh::lean_box(0);
                if v_isShared_4330_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4329_, 0, v___x_4352_);
                    v___x_4354_ = v___x_4329_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
                    v___x_4354_ = v_reuseFailAlloc_4355_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4354_;
            }
            9 => {
                if v_isShared_4362_ == 0 {
                    v___x_4364_ = v___x_4361_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
                    v___x_4364_ = v_reuseFailAlloc_4365_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4364_;
            }
            11 => {
                return v___x_4369_;
            }
            12 => {
                if v_isShared_4375_ == 0 {
                    v___x_4377_ = v___x_4374_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
                    v___x_4377_ = v_reuseFailAlloc_4378_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg___boxed(
    mut v_fvarId_4382_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
        v_fvarId_4382_,
        v_fvarId_x27_4383_,
        v_a_4384_,
        v_a_4385_,
        v_a_4386_,
        v_a_4387_,
        v_a_4388_,
    );
    crate::leanh::lean_dec(v_a_4388_);
    crate::leanh::lean_dec_ref(v_a_4387_);
    crate::leanh::lean_dec(v_a_4386_);
    crate::leanh::lean_dec_ref(v_a_4385_);
    crate::leanh::lean_dec(v_a_4384_);
    return v_res_4390_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFVarSubst(
    mut v_fvarId_4391_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_4392_: *mut crate::leanh::LeanObject,
    mut v_a_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4401_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
        v_fvarId_4391_,
        v_fvarId_x27_4392_,
        v_a_4394_,
        v_a_4396_,
        v_a_4397_,
        v_a_4398_,
        v_a_4399_,
    );
    return v___x_4401_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_addFVarSubst___boxed(
    mut v_fvarId_4402_: *mut crate::leanh::LeanObject,
    mut v_fvarId_x27_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
    mut v_a_4406_: *mut crate::leanh::LeanObject,
    mut v_a_4407_: *mut crate::leanh::LeanObject,
    mut v_a_4408_: *mut crate::leanh::LeanObject,
    mut v_a_4409_: *mut crate::leanh::LeanObject,
    mut v_a_4410_: *mut crate::leanh::LeanObject,
    mut v_a_4411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4412_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst(
        v_fvarId_4402_,
        v_fvarId_x27_4403_,
        v_a_4404_,
        v_a_4405_,
        v_a_4406_,
        v_a_4407_,
        v_a_4408_,
        v_a_4409_,
        v_a_4410_,
    );
    crate::leanh::lean_dec(v_a_4410_);
    crate::leanh::lean_dec_ref(v_a_4409_);
    crate::leanh::lean_dec(v_a_4408_);
    crate::leanh::lean_dec_ref(v_a_4407_);
    crate::leanh::lean_dec_ref(v_a_4406_);
    crate::leanh::lean_dec(v_a_4405_);
    crate::leanh::lean_dec_ref(v_a_4404_);
    return v_res_4412_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Renaming(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_Simp_instMonadSimpM = _init_l_Lean_Compiler_LCNF_Simp_instMonadSimpM();
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instMonadSimpM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_SimpM(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_SimpM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Renaming(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
}
