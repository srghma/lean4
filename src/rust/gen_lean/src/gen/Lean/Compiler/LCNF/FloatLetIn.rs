// Lean compiler output
// Module: Lean.Compiler.LCNF.FloatLetIn
// Imports: Lean.Compiler.LCNF.FVarUtil Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PhaseExt
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_List_lengthTR___redArg, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg, l_Lean_Compiler_LCNF_attachCodeDecls,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseCodeDecl___redArg, l_Lean_Compiler_LCNF_getPurity___redArg,
    l_Lean_Compiler_LCNF_getType, l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed,
    l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed,
};
use crate::r#gen::Lean::Compiler::LCNF::FVarUtil::{
    initialize_Lean_Compiler_LCNF_FVarUtil, runtime_initialize_Lean_Compiler_LCNF_FVarUtil,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg, l_Lean_Compiler_LCNF_instInhabitedPass,
    runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasFVar, l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_panic_fn_borrowed, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
static mut l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0: u64 = 0;
static mut l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1: u64 = 0;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 70,
        108, 111, 97, 116, 76, 101, 116, 73, 110, 46, 68, 101, 99, 105, 115, 105, 111, 110, 46,
        100, 101, 102, 97, 117, 108, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2_value:
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
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 70,
        108, 111, 97, 116, 76, 101, 116, 73, 110, 46, 68, 101, 99, 105, 115, 105, 111, 110, 46,
        100, 111, 110, 116, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 70,
        108, 111, 97, 116, 76, 101, 116, 73, 110, 46, 68, 101, 99, 105, 115, 105, 111, 110, 46,
        117, 110, 107, 110, 111, 119, 110, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6_value:
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
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 70,
        108, 111, 97, 116, 76, 101, 116, 73, 110, 46, 68, 101, 99, 105, 115, 105, 111, 110, 46, 97,
        114, 109, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__7_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 70, 86, 97, 114, 85, 116, 105, 108, 0]};
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 69, 120, 112, 114, 46, 102, 111, 114, 70, 86, 97, 114, 77, 0]};
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [102, 108, 111, 97, 116, 76, 101, 116, 73, 110, 0]};
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,8663532666736445726 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [83, 105, 122, 101, 32, 111, 102, 32, 99, 111, 100, 101, 32, 116, 104, 97, 116, 32, 119, 97, 115, 32, 112, 117, 115, 104, 101, 100, 32, 105, 110, 116, 111, 32, 97, 114, 109, 58, 32, 0]};
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,9045461525124583392 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_floatLetIn___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_floatLetIn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_floatLetIn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [70, 108, 111, 97, 116, 76, 101, 116, 73, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7565957283210374125 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6136635380946626520 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14687293079335206737 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,14766866284033629791 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17912384495688108754 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12008336300033170407 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8364664179798578562 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13092583406200651747 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,13855934446162426981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17378694802515979504 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17282638215117644296 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx(
    mut v_x_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4119_) {
        0 => {
            let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4120_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4120_;
        }
        1 => {
            let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4121_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4121_;
        }
        2 => {
            let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4122_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4122_;
        }
        _ => {
            let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4123_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_4123_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx___boxed(
    mut v_x_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4125_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorIdx(v_x_4124_);
    crate::leanh::lean_dec(v_x_4124_);
    return v_res_4125_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(
    mut v_t_4126_: *mut crate::leanh::LeanObject,
    mut v_k_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4126_) == 0 {
        let mut v_name_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_name_4128_ = crate::leanh::lean_ctor_get(v_t_4126_, 0);
        crate::leanh::lean_inc(v_name_4128_);
        crate::leanh::lean_dec_ref_known(v_t_4126_, 1);
        v___x_4129_ = crate::leanh::lean_apply_1(v_k_4127_, v_name_4128_);
        return v___x_4129_;
    } else {
        crate::leanh::lean_dec(v_t_4126_);
        return v_k_4127_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(
    mut v_motive_4130_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4131_: *mut crate::leanh::LeanObject,
    mut v_t_4132_: *mut crate::leanh::LeanObject,
    mut v_h_4133_: *mut crate::leanh::LeanObject,
    mut v_k_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4132_, v_k_4134_);
    return v___x_4135_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___boxed(
    mut v_motive_4136_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4137_: *mut crate::leanh::LeanObject,
    mut v_t_4138_: *mut crate::leanh::LeanObject,
    mut v_h_4139_: *mut crate::leanh::LeanObject,
    mut v_k_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4141_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim(
        v_motive_4136_,
        v_ctorIdx_4137_,
        v_t_4138_,
        v_h_4139_,
        v_k_4140_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4137_);
    return v_res_4141_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim___redArg(
    mut v_t_4142_: *mut crate::leanh::LeanObject,
    mut v_arm_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4144_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4142_, v_arm_4143_);
    return v___x_4144_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_arm_elim(
    mut v_motive_4145_: *mut crate::leanh::LeanObject,
    mut v_t_4146_: *mut crate::leanh::LeanObject,
    mut v_h_4147_: *mut crate::leanh::LeanObject,
    mut v_arm_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4149_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4146_, v_arm_4148_);
    return v___x_4149_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim___redArg(
    mut v_t_4150_: *mut crate::leanh::LeanObject,
    mut v_default_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4152_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4150_, v_default_4151_);
    return v___x_4152_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_default_elim(
    mut v_motive_4153_: *mut crate::leanh::LeanObject,
    mut v_t_4154_: *mut crate::leanh::LeanObject,
    mut v_h_4155_: *mut crate::leanh::LeanObject,
    mut v_default_4156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4157_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4154_, v_default_4156_);
    return v___x_4157_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim___redArg(
    mut v_t_4158_: *mut crate::leanh::LeanObject,
    mut v_dont_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4158_, v_dont_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_dont_elim(
    mut v_motive_4161_: *mut crate::leanh::LeanObject,
    mut v_t_4162_: *mut crate::leanh::LeanObject,
    mut v_h_4163_: *mut crate::leanh::LeanObject,
    mut v_dont_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4162_, v_dont_4164_);
    return v___x_4165_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim___redArg(
    mut v_t_4166_: *mut crate::leanh::LeanObject,
    mut v_unknown_4167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4168_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4166_, v_unknown_4167_);
    return v___x_4168_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_unknown_elim(
    mut v_motive_4169_: *mut crate::leanh::LeanObject,
    mut v_t_4170_: *mut crate::leanh::LeanObject,
    mut v_h_4171_: *mut crate::leanh::LeanObject,
    mut v_unknown_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4173_ =
        l_Lean_Compiler_LCNF_FloatLetIn_Decision_ctorElim___redArg(v_t_4170_, v_unknown_4172_);
    return v___x_4173_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0() -> u64 {
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: u64 = 0;
    v___x_4174_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4175_ = lean_uint64_of_nat(v___x_4174_);
    return v___x_4175_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1() -> u64 {
    let mut v___x_4176_: u64 = 0;
    let mut v___x_4177_: u64 = 0;
    let mut v___x_4178_: u64 = 0;
    v___x_4176_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__0,
    );
    v___x_4177_ = 0u64;
    v___x_4178_ = lean_uint64_mix_hash(v___x_4177_, v___x_4176_);
    return v___x_4178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(
    mut v_x_4179_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_4179_) {
        0 => {
            let mut v_name_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4181_: u64 = 0;
            v_name_4180_ = crate::leanh::lean_ctor_get(v_x_4179_, 0);
            v___x_4181_ = 0u64;
            if crate::leanh::lean_obj_tag(v_name_4180_) == 0 {
                let mut v___x_4182_: u64 = 0;
                v___x_4182_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___closed__1,
                );
                return v___x_4182_;
            } else {
                let mut v_hash_4183_: u64 = 0;
                let mut v___x_4184_: u64 = 0;
                v_hash_4183_ = crate::leanh::lean_ctor_get_uint64(
                    v_name_4180_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v___x_4184_ = lean_uint64_mix_hash(v___x_4181_, v_hash_4183_);
                return v___x_4184_;
            }
        }
        1 => {
            let mut v___x_4185_: u64 = 0;
            v___x_4185_ = 1u64;
            return v___x_4185_;
        }
        2 => {
            let mut v___x_4186_: u64 = 0;
            v___x_4186_ = 2u64;
            return v___x_4186_;
        }
        _ => {
            let mut v___x_4187_: u64 = 0;
            v___x_4187_ = 3u64;
            return v___x_4187_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash___boxed(
    mut v_x_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4189_: u64 = 0;
    let mut v_r_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4189_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_x_4188_);
    crate::leanh::lean_dec(v_x_4188_);
    v_r_4190_ = crate::leanh::lean_box_uint64(v_res_4189_);
    return v_r_4190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(
    mut v_x_4193_: *mut crate::leanh::LeanObject,
    mut v_x_4194_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_4193_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_4194_) == 0 {
                let mut v_name_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_name_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4197_: u8 = 0;
                v_name_4195_ = crate::leanh::lean_ctor_get(v_x_4193_, 0);
                v_name_4196_ = crate::leanh::lean_ctor_get(v_x_4194_, 0);
                v___x_4197_ = lean_name_eq(v_name_4195_, v_name_4196_);
                return v___x_4197_;
            } else {
                let mut v___x_4198_: u8 = 0;
                v___x_4198_ = 0;
                return v___x_4198_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_4194_) == 1 {
                let mut v___x_4199_: u8 = 0;
                v___x_4199_ = 1;
                return v___x_4199_;
            } else {
                let mut v___x_4200_: u8 = 0;
                v___x_4200_ = 0;
                return v___x_4200_;
            }
        }
        2 => {
            if crate::leanh::lean_obj_tag(v_x_4194_) == 2 {
                let mut v___x_4201_: u8 = 0;
                v___x_4201_ = 1;
                return v___x_4201_;
            } else {
                let mut v___x_4202_: u8 = 0;
                v___x_4202_ = 0;
                return v___x_4202_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_4194_) == 3 {
                let mut v___x_4203_: u8 = 0;
                v___x_4203_ = 1;
                return v___x_4203_;
            } else {
                let mut v___x_4204_: u8 = 0;
                v___x_4204_ = 0;
                return v___x_4204_;
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq___boxed(
    mut v_x_4205_: *mut crate::leanh::LeanObject,
    mut v_x_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4207_: u8 = 0;
    let mut v_r_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_x_4205_, v_x_4206_);
    crate::leanh::lean_dec(v_x_4206_);
    crate::leanh::lean_dec(v_x_4205_);
    v_r_4208_ = crate::leanh::lean_box((v_res_4207_) as usize);
    return v_r_4208_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4231_ = lean_nat_to_int(v___x_4230_);
    return v___x_4231_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4232_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4233_ = lean_nat_to_int(v___x_4232_);
    return v___x_4233_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(
    mut v_x_4234_: *mut crate::leanh::LeanObject,
    mut v_prec_4235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: u8 = 0;
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: u8 = 0;
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: u8 = 0;
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: u8 = 0;
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4234_) {
                0 => {
                    v_name_4257_ = crate::leanh::lean_ctor_get(v_x_4234_, 0);
                    crate::leanh::lean_inc(v_name_4257_);
                    crate::leanh::lean_dec_ref_known(v_x_4234_, 1);
                    v___x_4268_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4269_ = lean_nat_dec_le(v___x_4268_, v_prec_4235_);
                    if v___x_4269_ == 0 {
                        v___x_4270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
                        v___y_4259_ = v___x_4270_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4271_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
                        v___y_4259_ = v___x_4271_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v___x_4272_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4273_ = lean_nat_dec_le(v___x_4272_, v_prec_4235_);
                    if v___x_4273_ == 0 {
                        v___x_4274_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
                        v___y_4237_ = v___x_4274_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
                        v___y_4237_ = v___x_4275_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v___x_4276_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4277_ = lean_nat_dec_le(v___x_4276_, v_prec_4235_);
                    if v___x_4277_ == 0 {
                        v___x_4278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
                        v___y_4244_ = v___x_4278_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
                        v___y_4244_ = v___x_4279_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_4280_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4281_ = lean_nat_dec_le(v___x_4280_, v_prec_4235_);
                    if v___x_4281_ == 0 {
                        v___x_4282_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__9);
                        v___y_4251_ = v___x_4282_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4283_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10_once), _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__10);
                        v___y_4251_ = v___x_4283_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4238_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__1;
                crate::leanh::lean_inc(v___y_4237_);
                v___x_4239_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4239_, 0, v___y_4237_);
                crate::leanh::lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                v___x_4240_ = 0;
                v___x_4241_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4241_, 0, v___x_4239_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4241_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4240_,
                );
                v___x_4242_ = l_Repr_addAppParen(v___x_4241_, v_prec_4235_);
                return v___x_4242_;
            }
            2 => {
                v___x_4245_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__3;
                crate::leanh::lean_inc(v___y_4244_);
                v___x_4246_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4246_, 0, v___y_4244_);
                crate::leanh::lean_ctor_set(v___x_4246_, 1, v___x_4245_);
                v___x_4247_ = 0;
                v___x_4248_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4248_, 0, v___x_4246_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4248_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4247_,
                );
                v___x_4249_ = l_Repr_addAppParen(v___x_4248_, v_prec_4235_);
                return v___x_4249_;
            }
            3 => {
                v___x_4252_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__5;
                crate::leanh::lean_inc(v___y_4251_);
                v___x_4253_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4253_, 0, v___y_4251_);
                crate::leanh::lean_ctor_set(v___x_4253_, 1, v___x_4252_);
                v___x_4254_ = 0;
                v___x_4255_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4255_, 0, v___x_4253_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4255_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4254_,
                );
                v___x_4256_ = l_Repr_addAppParen(v___x_4255_, v_prec_4235_);
                return v___x_4256_;
            }
            4 => {
                v___x_4260_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___closed__8;
                v___x_4261_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4262_ = l_Lean_Name_reprPrec(v_name_4257_, v___x_4261_);
                v___x_4263_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4263_, 0, v___x_4260_);
                crate::leanh::lean_ctor_set(v___x_4263_, 1, v___x_4262_);
                crate::leanh::lean_inc(v___y_4259_);
                v___x_4264_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4264_, 0, v___y_4259_);
                crate::leanh::lean_ctor_set(v___x_4264_, 1, v___x_4263_);
                v___x_4265_ = 0;
                v___x_4266_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4266_, 0, v___x_4264_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4266_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4265_,
                );
                v___x_4267_ = l_Repr_addAppParen(v___x_4266_, v_prec_4235_);
                return v___x_4267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr___boxed(
    mut v_x_4284_: *mut crate::leanh::LeanObject,
    mut v_prec_4285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(v_x_4284_, v_prec_4285_);
    crate::leanh::lean_dec(v_prec_4285_);
    return v_res_4286_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(
    mut v_x_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4289_) == 0 {
        let mut v_ctorName_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ctorName_4290_ = crate::leanh::lean_ctor_get(v_x_4289_, 0);
        crate::leanh::lean_inc(v_ctorName_4290_);
        v___x_4291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4291_, 0, v_ctorName_4290_);
        return v___x_4291_;
    } else {
        let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4292_ = crate::leanh::lean_box(1);
        return v___x_4292_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(
    mut v_x_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4294_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_x_4293_);
    crate::leanh::lean_dec_ref(v_x_4293_);
    return v_res_4294_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(
    mut v_decl_4295_: *mut crate::leanh::LeanObject,
    mut v_x_4296_: *mut crate::leanh::LeanObject,
    mut v_a_4297_: *mut crate::leanh::LeanObject,
    mut v_a_4298_: *mut crate::leanh::LeanObject,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_4297_);
    v___x_4303_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4303_, 0, v_decl_4295_);
    crate::leanh::lean_ctor_set(v___x_4303_, 1, v_a_4297_);
    crate::leanh::lean_inc(v_a_4301_);
    crate::leanh::lean_inc_ref(v_a_4300_);
    crate::leanh::lean_inc(v_a_4299_);
    crate::leanh::lean_inc_ref(v_a_4298_);
    v___x_4304_ = crate::leanh::lean_apply_6(
        v_x_4296_,
        v___x_4303_,
        v_a_4298_,
        v_a_4299_,
        v_a_4300_,
        v_a_4301_,
        crate::leanh::lean_box(0),
    );
    return v___x_4304_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg___boxed(
    mut v_decl_4305_: *mut crate::leanh::LeanObject,
    mut v_x_4306_: *mut crate::leanh::LeanObject,
    mut v_a_4307_: *mut crate::leanh::LeanObject,
    mut v_a_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4313_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(
        v_decl_4305_,
        v_x_4306_,
        v_a_4307_,
        v_a_4308_,
        v_a_4309_,
        v_a_4310_,
        v_a_4311_,
    );
    crate::leanh::lean_dec(v_a_4311_);
    crate::leanh::lean_dec_ref(v_a_4310_);
    crate::leanh::lean_dec(v_a_4309_);
    crate::leanh::lean_dec_ref(v_a_4308_);
    crate::leanh::lean_dec(v_a_4307_);
    return v_res_4313_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(
    mut v_00_u03b1_4314_: *mut crate::leanh::LeanObject,
    mut v_decl_4315_: *mut crate::leanh::LeanObject,
    mut v_x_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
    mut v_a_4320_: *mut crate::leanh::LeanObject,
    mut v_a_4321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4323_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(
        v_decl_4315_,
        v_x_4316_,
        v_a_4317_,
        v_a_4318_,
        v_a_4319_,
        v_a_4320_,
        v_a_4321_,
    );
    return v___x_4323_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___boxed(
    mut v_00_u03b1_4324_: *mut crate::leanh::LeanObject,
    mut v_decl_4325_: *mut crate::leanh::LeanObject,
    mut v_x_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
    mut v_a_4328_: *mut crate::leanh::LeanObject,
    mut v_a_4329_: *mut crate::leanh::LeanObject,
    mut v_a_4330_: *mut crate::leanh::LeanObject,
    mut v_a_4331_: *mut crate::leanh::LeanObject,
    mut v_a_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4333_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(
        v_00_u03b1_4324_,
        v_decl_4325_,
        v_x_4326_,
        v_a_4327_,
        v_a_4328_,
        v_a_4329_,
        v_a_4330_,
        v_a_4331_,
    );
    crate::leanh::lean_dec(v_a_4331_);
    crate::leanh::lean_dec_ref(v_a_4330_);
    crate::leanh::lean_dec(v_a_4329_);
    crate::leanh::lean_dec_ref(v_a_4328_);
    crate::leanh::lean_dec(v_a_4327_);
    return v_res_4333_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(
    mut v_x_4334_: *mut crate::leanh::LeanObject,
    mut v_a_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4340_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_a_4338_);
    crate::leanh::lean_inc_ref(v_a_4337_);
    crate::leanh::lean_inc(v_a_4336_);
    crate::leanh::lean_inc_ref(v_a_4335_);
    v___x_4341_ = crate::leanh::lean_apply_6(
        v_x_4334_,
        v___x_4340_,
        v_a_4335_,
        v_a_4336_,
        v_a_4337_,
        v_a_4338_,
        crate::leanh::lean_box(0),
    );
    return v___x_4341_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg___boxed(
    mut v_x_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_a_4344_: *mut crate::leanh::LeanObject,
    mut v_a_4345_: *mut crate::leanh::LeanObject,
    mut v_a_4346_: *mut crate::leanh::LeanObject,
    mut v_a_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4348_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(
        v_x_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_,
    );
    crate::leanh::lean_dec(v_a_4346_);
    crate::leanh::lean_dec_ref(v_a_4345_);
    crate::leanh::lean_dec(v_a_4344_);
    crate::leanh::lean_dec_ref(v_a_4343_);
    return v_res_4348_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(
    mut v_00_u03b1_4349_: *mut crate::leanh::LeanObject,
    mut v_x_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
    mut v_a_4355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4357_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(
        v_x_4350_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_,
    );
    return v___x_4357_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(
    mut v_00_u03b1_4358_: *mut crate::leanh::LeanObject,
    mut v_x_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(
        v_00_u03b1_4358_,
        v_x_4359_,
        v_a_4360_,
        v_a_4361_,
        v_a_4362_,
        v_a_4363_,
        v_a_4364_,
    );
    crate::leanh::lean_dec(v_a_4364_);
    crate::leanh::lean_dec_ref(v_a_4363_);
    crate::leanh::lean_dec(v_a_4362_);
    crate::leanh::lean_dec_ref(v_a_4361_);
    crate::leanh::lean_dec(v_a_4360_);
    return v_res_4366_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(
    mut v_decl_4367_: *mut crate::leanh::LeanObject,
    mut v_a_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4380_: u8 = 0;
    let mut v_struct_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4388_: u8 = 0;
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_a_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_a_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4424_: u8 = 0;
    let mut v_a_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_4373_ = crate::leanh::lean_ctor_get(v_decl_4367_, 2);
                crate::leanh::lean_inc_ref(v_type_4373_);
                v_value_4374_ = crate::leanh::lean_ctor_get(v_decl_4367_, 3);
                crate::leanh::lean_inc(v_value_4374_);
                crate::leanh::lean_dec_ref(v_decl_4367_);
                v___x_4375_ =
                    l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(v_type_4373_, v_a_4371_);
                if crate::leanh::lean_obj_tag(v___x_4375_) == 0 {
                    v_a_4376_ = crate::leanh::lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4424_ = (!crate::leanh::lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4424_ == 0 {
                        v___x_4378_ = v___x_4375_;
                        v_isShared_4379_ = v_isSharedCheck_4424_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4376_);
                        crate::leanh::lean_dec(v___x_4375_);
                        v___x_4378_ = crate::leanh::lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4424_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4374_);
                    v_a_4425_ = crate::leanh::lean_ctor_get(v___x_4375_, 0);
                    v_isSharedCheck_4432_ = (!crate::leanh::lean_is_exclusive(v___x_4375_)) as u8;
                    if v_isSharedCheck_4432_ == 0 {
                        v___x_4427_ = v___x_4375_;
                        v_isShared_4428_ = v_isSharedCheck_4432_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4425_);
                        crate::leanh::lean_dec(v___x_4375_);
                        v___x_4427_ = crate::leanh::lean_box(0);
                        v_isShared_4428_ = v_isSharedCheck_4432_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4376_) == 0 {
                    v___x_4380_ = 0;
                    if crate::leanh::lean_obj_tag(v_value_4374_) == 2 {
                        crate::leanh::lean_del_object(v___x_4378_);
                        v_struct_4381_ = crate::leanh::lean_ctor_get(v_value_4374_, 2);
                        crate::leanh::lean_inc(v_struct_4381_);
                        crate::leanh::lean_dec_ref_known(v_value_4374_, 3);
                        v___x_4382_ = l_Lean_Compiler_LCNF_getType(
                            v_struct_4381_,
                            v_a_4368_,
                            v_a_4369_,
                            v_a_4370_,
                            v_a_4371_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4382_) == 0 {
                            v_a_4383_ = crate::leanh::lean_ctor_get(v___x_4382_, 0);
                            crate::leanh::lean_inc(v_a_4383_);
                            crate::leanh::lean_dec_ref_known(v___x_4382_, 1);
                            v___x_4384_ = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(
                                v_a_4383_, v_a_4371_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4384_) == 0 {
                                v_a_4385_ = crate::leanh::lean_ctor_get(v___x_4384_, 0);
                                v_isSharedCheck_4398_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4384_)) as u8;
                                if v_isSharedCheck_4398_ == 0 {
                                    v___x_4387_ = v___x_4384_;
                                    v_isShared_4388_ = v_isSharedCheck_4398_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4385_);
                                    crate::leanh::lean_dec(v___x_4384_);
                                    v___x_4387_ = crate::leanh::lean_box(0);
                                    v_isShared_4388_ = v_isSharedCheck_4398_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_4399_ = crate::leanh::lean_ctor_get(v___x_4384_, 0);
                                v_isSharedCheck_4406_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4384_)) as u8;
                                if v_isSharedCheck_4406_ == 0 {
                                    v___x_4401_ = v___x_4384_;
                                    v_isShared_4402_ = v_isSharedCheck_4406_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4399_);
                                    crate::leanh::lean_dec(v___x_4384_);
                                    v___x_4401_ = crate::leanh::lean_box(0);
                                    v_isShared_4402_ = v_isSharedCheck_4406_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4407_ = crate::leanh::lean_ctor_get(v___x_4382_, 0);
                            v_isSharedCheck_4414_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4382_)) as u8;
                            if v_isSharedCheck_4414_ == 0 {
                                v___x_4409_ = v___x_4382_;
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4407_);
                                crate::leanh::lean_dec(v___x_4382_);
                                v___x_4409_ = crate::leanh::lean_box(0);
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_value_4374_);
                        v___x_4415_ = crate::leanh::lean_box((v___x_4380_) as usize);
                        if v_isShared_4379_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4378_, 0, v___x_4415_);
                            v___x_4417_ = v___x_4378_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4418_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
                            v___x_4417_ = v_reuseFailAlloc_4418_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_4376_, 1);
                    crate::leanh::lean_dec(v_value_4374_);
                    v___x_4419_ = 1;
                    v___x_4420_ = crate::leanh::lean_box((v___x_4419_) as usize);
                    if v_isShared_4379_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4378_, 0, v___x_4420_);
                        v___x_4422_ = v___x_4378_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
                        v___x_4422_ = v_reuseFailAlloc_4423_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4385_) == 0 {
                    v___x_4389_ = crate::leanh::lean_box((v___x_4380_) as usize);
                    if v_isShared_4388_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4389_);
                        v___x_4391_ = v___x_4387_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4392_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 0, v___x_4389_);
                        v___x_4391_ = v_reuseFailAlloc_4392_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_4385_, 1);
                    v___x_4393_ = 1;
                    v___x_4394_ = crate::leanh::lean_box((v___x_4393_) as usize);
                    if v_isShared_4388_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4394_);
                        v___x_4396_ = v___x_4387_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4397_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v___x_4394_);
                        v___x_4396_ = v_reuseFailAlloc_4397_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4391_;
            }
            4 => {
                return v___x_4396_;
            }
            5 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4404_;
            }
            7 => {
                if v_isShared_4410_ == 0 {
                    v___x_4412_ = v___x_4409_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
                    v___x_4412_ = v_reuseFailAlloc_4413_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4412_;
            }
            9 => {
                return v___x_4417_;
            }
            10 => {
                return v___x_4422_;
            }
            11 => {
                if v_isShared_4428_ == 0 {
                    v___x_4430_ = v___x_4427_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
                    v___x_4430_ = v_reuseFailAlloc_4431_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(
    mut v_decl_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_a_4435_: *mut crate::leanh::LeanObject,
    mut v_a_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(
        v_decl_4433_,
        v_a_4434_,
        v_a_4435_,
        v_a_4436_,
        v_a_4437_,
    );
    crate::leanh::lean_dec(v_a_4437_);
    crate::leanh::lean_dec_ref(v_a_4436_);
    crate::leanh::lean_dec(v_a_4435_);
    crate::leanh::lean_dec_ref(v_a_4434_);
    return v_res_4439_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(
    mut v_decl_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v_a_4442_: *mut crate::leanh::LeanObject,
    mut v_a_4443_: *mut crate::leanh::LeanObject,
    mut v_a_4444_: *mut crate::leanh::LeanObject,
    mut v_a_4445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4447_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(
        v_decl_4440_,
        v_a_4442_,
        v_a_4443_,
        v_a_4444_,
        v_a_4445_,
    );
    return v___x_4447_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(
    mut v_decl_4448_: *mut crate::leanh::LeanObject,
    mut v_a_4449_: *mut crate::leanh::LeanObject,
    mut v_a_4450_: *mut crate::leanh::LeanObject,
    mut v_a_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
    mut v_a_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4455_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(
        v_decl_4448_,
        v_a_4449_,
        v_a_4450_,
        v_a_4451_,
        v_a_4452_,
        v_a_4453_,
    );
    crate::leanh::lean_dec(v_a_4453_);
    crate::leanh::lean_dec_ref(v_a_4452_);
    crate::leanh::lean_dec(v_a_4451_);
    crate::leanh::lean_dec_ref(v_a_4450_);
    crate::leanh::lean_dec(v_a_4449_);
    return v_res_4455_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(
    mut v_a_4456_: *mut crate::leanh::LeanObject,
    mut v_x_4457_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4458_: u8 = 0;
    let mut v_key_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4457_) == 0 {
                    v___x_4458_ = 0;
                    return v___x_4458_;
                } else {
                    v_key_4459_ = crate::leanh::lean_ctor_get(v_x_4457_, 0);
                    v_tail_4460_ = crate::leanh::lean_ctor_get(v_x_4457_, 2);
                    v___x_4461_ = l_Lean_instBEqFVarId_beq(v_key_4459_, v_a_4456_);
                    if v___x_4461_ == 0 {
                        v_x_4457_ = v_tail_4460_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4461_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg___boxed(
    mut v_a_4463_: *mut crate::leanh::LeanObject,
    mut v_x_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: u8 = 0;
    let mut v_r_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_4463_, v_x_4464_);
    crate::leanh::lean_dec(v_x_4464_);
    crate::leanh::lean_dec(v_a_4463_);
    v_r_4466_ = crate::leanh::lean_box((v_res_4465_) as usize);
    return v_r_4466_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(
    mut v_m_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u64 = 0;
    let mut v___x_4472_: u64 = 0;
    let mut v___x_4473_: u64 = 0;
    let mut v_fold_4474_: u64 = 0;
    let mut v___x_4475_: u64 = 0;
    let mut v___x_4476_: u64 = 0;
    let mut v___x_4477_: u64 = 0;
    let mut v___x_4478_: usize = 0;
    let mut v___x_4479_: usize = 0;
    let mut v___x_4480_: usize = 0;
    let mut v___x_4481_: usize = 0;
    let mut v___x_4482_: usize = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: u8 = 0;
    v_buckets_4469_ = crate::leanh::lean_ctor_get(v_m_4467_, 1);
    v___x_4470_ = lean_array_get_size(v_buckets_4469_);
    v___x_4471_ = l_Lean_instHashableFVarId_hash(v_a_4468_);
    v___x_4472_ = 32u64;
    v___x_4473_ = lean_uint64_shift_right(v___x_4471_, v___x_4472_);
    v_fold_4474_ = lean_uint64_xor(v___x_4471_, v___x_4473_);
    v___x_4475_ = 16u64;
    v___x_4476_ = lean_uint64_shift_right(v_fold_4474_, v___x_4475_);
    v___x_4477_ = lean_uint64_xor(v_fold_4474_, v___x_4476_);
    v___x_4478_ = lean_uint64_to_usize(v___x_4477_);
    v___x_4479_ = lean_usize_of_nat(v___x_4470_);
    v___x_4480_ = 1usize;
    v___x_4481_ = lean_usize_sub(v___x_4479_, v___x_4480_);
    v___x_4482_ = lean_usize_land(v___x_4478_, v___x_4481_);
    v___x_4483_ = lean_array_uget_borrowed(v_buckets_4469_, v___x_4482_);
    v___x_4484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_4468_, v___x_4483_);
    return v___x_4484_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg___boxed(
    mut v_m_4485_: *mut crate::leanh::LeanObject,
    mut v_a_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4487_: u8 = 0;
    let mut v_r_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4487_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_4485_, v_a_4486_);
    crate::leanh::lean_dec(v_a_4486_);
    crate::leanh::lean_dec_ref(v_m_4485_);
    v_r_4488_ = crate::leanh::lean_box((v_res_4487_) as usize);
    return v_r_4488_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_4489_: *mut crate::leanh::LeanObject,
    mut v_x_4490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4496_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u64 = 0;
    let mut v___x_4499_: u64 = 0;
    let mut v___x_4500_: u64 = 0;
    let mut v_fold_4501_: u64 = 0;
    let mut v___x_4502_: u64 = 0;
    let mut v___x_4503_: u64 = 0;
    let mut v___x_4504_: u64 = 0;
    let mut v___x_4505_: usize = 0;
    let mut v___x_4506_: usize = 0;
    let mut v___x_4507_: usize = 0;
    let mut v___x_4508_: usize = 0;
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4490_) == 0 {
                    return v_x_4489_;
                } else {
                    v_key_4491_ = crate::leanh::lean_ctor_get(v_x_4490_, 0);
                    v_value_4492_ = crate::leanh::lean_ctor_get(v_x_4490_, 1);
                    v_tail_4493_ = crate::leanh::lean_ctor_get(v_x_4490_, 2);
                    v_isSharedCheck_4516_ = (!crate::leanh::lean_is_exclusive(v_x_4490_)) as u8;
                    if v_isSharedCheck_4516_ == 0 {
                        v___x_4495_ = v_x_4490_;
                        v_isShared_4496_ = v_isSharedCheck_4516_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4493_);
                        crate::leanh::lean_inc(v_value_4492_);
                        crate::leanh::lean_inc(v_key_4491_);
                        crate::leanh::lean_dec(v_x_4490_);
                        v___x_4495_ = crate::leanh::lean_box(0);
                        v_isShared_4496_ = v_isSharedCheck_4516_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4497_ = lean_array_get_size(v_x_4489_);
                v___x_4498_ = l_Lean_instHashableFVarId_hash(v_key_4491_);
                v___x_4499_ = 32u64;
                v___x_4500_ = lean_uint64_shift_right(v___x_4498_, v___x_4499_);
                v_fold_4501_ = lean_uint64_xor(v___x_4498_, v___x_4500_);
                v___x_4502_ = 16u64;
                v___x_4503_ = lean_uint64_shift_right(v_fold_4501_, v___x_4502_);
                v___x_4504_ = lean_uint64_xor(v_fold_4501_, v___x_4503_);
                v___x_4505_ = lean_uint64_to_usize(v___x_4504_);
                v___x_4506_ = lean_usize_of_nat(v___x_4497_);
                v___x_4507_ = 1usize;
                v___x_4508_ = lean_usize_sub(v___x_4506_, v___x_4507_);
                v___x_4509_ = lean_usize_land(v___x_4505_, v___x_4508_);
                v___x_4510_ = lean_array_uget_borrowed(v_x_4489_, v___x_4509_);
                crate::leanh::lean_inc(v___x_4510_);
                if v_isShared_4496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4495_, 2, v___x_4510_);
                    v___x_4512_ = v___x_4495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4515_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_key_4491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_value_4492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4515_, 2, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4515_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4513_ = lean_array_uset(v_x_4489_, v___x_4509_, v___x_4512_);
                v_x_4489_ = v___x_4513_;
                v_x_4490_ = v_tail_4493_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(
    mut v_i_4517_: *mut crate::leanh::LeanObject,
    mut v_source_4518_: *mut crate::leanh::LeanObject,
    mut v_target_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    let mut v_es_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4520_ = lean_array_get_size(v_source_4518_);
                v___x_4521_ = lean_nat_dec_lt(v_i_4517_, v___x_4520_);
                if v___x_4521_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4518_);
                    crate::leanh::lean_dec(v_i_4517_);
                    return v_target_4519_;
                } else {
                    v_es_4522_ = lean_array_fget(v_source_4518_, v_i_4517_);
                    v___x_4523_ = crate::leanh::lean_box(0);
                    v_source_4524_ = lean_array_fset(v_source_4518_, v_i_4517_, v___x_4523_);
                    v_target_4525_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_target_4519_, v_es_4522_);
                    v___x_4526_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4527_ = lean_nat_add(v_i_4517_, v___x_4526_);
                    crate::leanh::lean_dec(v_i_4517_);
                    v_i_4517_ = v___x_4527_;
                    v_source_4518_ = v_source_4524_;
                    v_target_4519_ = v_target_4525_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(
    mut v_data_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4530_ = lean_array_get_size(v_data_4529_);
    v___x_4531_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4532_ = lean_nat_mul(v___x_4530_, v___x_4531_);
    v___x_4533_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4534_ = crate::leanh::lean_box(0);
    v___x_4535_ = lean_mk_array(v_nbuckets_4532_, v___x_4534_);
    v___x_4536_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v___x_4533_, v_data_4529_, v___x_4535_);
    return v___x_4536_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(
    mut v_m_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_b_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: u64 = 0;
    let mut v___x_4544_: u64 = 0;
    let mut v___x_4545_: u64 = 0;
    let mut v_fold_4546_: u64 = 0;
    let mut v___x_4547_: u64 = 0;
    let mut v___x_4548_: u64 = 0;
    let mut v___x_4549_: u64 = 0;
    let mut v___x_4550_: usize = 0;
    let mut v___x_4551_: usize = 0;
    let mut v___x_4552_: usize = 0;
    let mut v___x_4553_: usize = 0;
    let mut v___x_4554_: usize = 0;
    let mut v_bkt_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: u8 = 0;
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v_val_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4577_: u8 = 0;
    let mut v_unused_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4540_ = crate::leanh::lean_ctor_get(v_m_4537_, 0);
                v_buckets_4541_ = crate::leanh::lean_ctor_get(v_m_4537_, 1);
                v___x_4542_ = lean_array_get_size(v_buckets_4541_);
                v___x_4543_ = l_Lean_instHashableFVarId_hash(v_a_4538_);
                v___x_4544_ = 32u64;
                v___x_4545_ = lean_uint64_shift_right(v___x_4543_, v___x_4544_);
                v_fold_4546_ = lean_uint64_xor(v___x_4543_, v___x_4545_);
                v___x_4547_ = 16u64;
                v___x_4548_ = lean_uint64_shift_right(v_fold_4546_, v___x_4547_);
                v___x_4549_ = lean_uint64_xor(v_fold_4546_, v___x_4548_);
                v___x_4550_ = lean_uint64_to_usize(v___x_4549_);
                v___x_4551_ = lean_usize_of_nat(v___x_4542_);
                v___x_4552_ = 1usize;
                v___x_4553_ = lean_usize_sub(v___x_4551_, v___x_4552_);
                v___x_4554_ = lean_usize_land(v___x_4550_, v___x_4553_);
                v_bkt_4555_ = lean_array_uget_borrowed(v_buckets_4541_, v___x_4554_);
                v___x_4556_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_4538_, v_bkt_4555_);
                if v___x_4556_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4541_);
                    crate::leanh::lean_inc(v_size_4540_);
                    v_isSharedCheck_4577_ = (!crate::leanh::lean_is_exclusive(v_m_4537_)) as u8;
                    if v_isSharedCheck_4577_ == 0 {
                        v_unused_4578_ = crate::leanh::lean_ctor_get(v_m_4537_, 1);
                        crate::leanh::lean_dec(v_unused_4578_);
                        v_unused_4579_ = crate::leanh::lean_ctor_get(v_m_4537_, 0);
                        crate::leanh::lean_dec(v_unused_4579_);
                        v___x_4558_ = v_m_4537_;
                        v_isShared_4559_ = v_isSharedCheck_4577_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4537_);
                        v___x_4558_ = crate::leanh::lean_box(0);
                        v_isShared_4559_ = v_isSharedCheck_4577_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4539_);
                    crate::leanh::lean_dec(v_a_4538_);
                    return v_m_4537_;
                }
            }
            1 => {
                v___x_4560_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4561_ = lean_nat_add(v_size_4540_, v___x_4560_);
                crate::leanh::lean_dec(v_size_4540_);
                crate::leanh::lean_inc(v_bkt_4555_);
                v___x_4562_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4562_, 0, v_a_4538_);
                crate::leanh::lean_ctor_set(v___x_4562_, 1, v_b_4539_);
                crate::leanh::lean_ctor_set(v___x_4562_, 2, v_bkt_4555_);
                v_buckets_x27_4563_ = lean_array_uset(v_buckets_4541_, v___x_4554_, v___x_4562_);
                v___x_4564_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4565_ = lean_nat_mul(v_size_x27_4561_, v___x_4564_);
                v___x_4566_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4567_ = lean_nat_div(v___x_4565_, v___x_4566_);
                crate::leanh::lean_dec(v___x_4565_);
                v___x_4568_ = lean_array_get_size(v_buckets_x27_4563_);
                v___x_4569_ = lean_nat_dec_le(v___x_4567_, v___x_4568_);
                crate::leanh::lean_dec(v___x_4567_);
                if v___x_4569_ == 0 {
                    v_val_4570_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_4563_);
                    if v_isShared_4559_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4558_, 1, v_val_4570_);
                        crate::leanh::lean_ctor_set(v___x_4558_, 0, v_size_x27_4561_);
                        v___x_4572_ = v___x_4558_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_size_x27_4561_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 1, v_val_4570_);
                        v___x_4572_ = v_reuseFailAlloc_4573_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4559_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4558_, 1, v_buckets_x27_4563_);
                        crate::leanh::lean_ctor_set(v___x_4558_, 0, v_size_x27_4561_);
                        v___x_4575_ = v___x_4558_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_size_x27_4561_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4576_, 1, v_buckets_x27_4563_);
                        v___x_4575_ = v_reuseFailAlloc_4576_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4572_;
            }
            3 => {
                return v___x_4575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(
    mut v_var_4580_: *mut crate::leanh::LeanObject,
    mut v_borrowed_4581_: u8,
    mut v_a_4582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_var_4580_) == 1 {
                    v_fvarId_4584_ = crate::leanh::lean_ctor_get(v_var_4580_, 0);
                    v_isSharedCheck_4602_ = (!crate::leanh::lean_is_exclusive(v_var_4580_)) as u8;
                    if v_isSharedCheck_4602_ == 0 {
                        v___x_4586_ = v_var_4580_;
                        v_isShared_4587_ = v_isSharedCheck_4602_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4584_);
                        crate::leanh::lean_dec(v_var_4580_);
                        v___x_4586_ = crate::leanh::lean_box(0);
                        v_isShared_4587_ = v_isSharedCheck_4602_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_var_4580_);
                    v___x_4603_ = 0;
                    v___x_4604_ = crate::leanh::lean_box((v___x_4603_) as usize);
                    v___x_4605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4605_, 0, v___x_4604_);
                    return v___x_4605_;
                }
            }
            1 => {
                v___x_4588_ = lean_st_ref_get(v_a_4582_);
                v___x_4589_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v___x_4588_, v_fvarId_4584_);
                crate::leanh::lean_dec(v___x_4588_);
                if v_borrowed_4581_ == 0 {
                    v___x_4590_ = lean_st_ref_take(v_a_4582_);
                    v___x_4591_ = crate::leanh::lean_box(0);
                    v___x_4592_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v___x_4590_, v_fvarId_4584_, v___x_4591_);
                    v___x_4593_ = lean_st_ref_set(v_a_4582_, v___x_4592_);
                    v___x_4594_ = crate::leanh::lean_box((v___x_4589_) as usize);
                    if v_isShared_4587_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4586_, 0);
                        crate::leanh::lean_ctor_set(v___x_4586_, 0, v___x_4594_);
                        v___x_4596_ = v___x_4586_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
                        v___x_4596_ = v_reuseFailAlloc_4597_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_4584_);
                    v___x_4598_ = crate::leanh::lean_box((v___x_4589_) as usize);
                    if v_isShared_4587_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4586_, 0);
                        crate::leanh::lean_ctor_set(v___x_4586_, 0, v___x_4598_);
                        v___x_4600_ = v___x_4586_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
                        v___x_4600_ = v_reuseFailAlloc_4601_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4596_;
            }
            3 => {
                return v___x_4600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg___boxed(
    mut v_var_4606_: *mut crate::leanh::LeanObject,
    mut v_borrowed_4607_: *mut crate::leanh::LeanObject,
    mut v_a_4608_: *mut crate::leanh::LeanObject,
    mut v_a_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_borrowed_boxed_4610_: u8 = 0;
    let mut v_res_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_borrowed_boxed_4610_ = (crate::leanh::lean_unbox(v_borrowed_4607_) as u8);
    v_res_4611_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_4606_, v_borrowed_boxed_4610_, v_a_4608_);
    crate::leanh::lean_dec(v_a_4608_);
    return v_res_4611_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(
    mut v_var_4612_: *mut crate::leanh::LeanObject,
    mut v_borrowed_4613_: u8,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_a_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
    mut v_a_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v_var_4612_, v_borrowed_4613_, v_a_4614_);
    return v___x_4620_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___boxed(
    mut v_var_4621_: *mut crate::leanh::LeanObject,
    mut v_borrowed_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_a_4626_: *mut crate::leanh::LeanObject,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_borrowed_boxed_4629_: u8 = 0;
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_borrowed_boxed_4629_ = (crate::leanh::lean_unbox(v_borrowed_4622_) as u8);
    v_res_4630_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg(v_var_4621_, v_borrowed_boxed_4629_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_);
    crate::leanh::lean_dec(v_a_4627_);
    crate::leanh::lean_dec_ref(v_a_4626_);
    crate::leanh::lean_dec(v_a_4625_);
    crate::leanh::lean_dec_ref(v_a_4624_);
    crate::leanh::lean_dec(v_a_4623_);
    return v_res_4630_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(
    mut v_00_u03b2_4631_: *mut crate::leanh::LeanObject,
    mut v_m_4632_: *mut crate::leanh::LeanObject,
    mut v_a_4633_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4634_: u8 = 0;
    v___x_4634_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_m_4632_, v_a_4633_);
    return v___x_4634_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___boxed(
    mut v_00_u03b2_4635_: *mut crate::leanh::LeanObject,
    mut v_m_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4638_: u8 = 0;
    let mut v_r_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4638_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0(v_00_u03b2_4635_, v_m_4636_, v_a_4637_);
    crate::leanh::lean_dec(v_a_4637_);
    crate::leanh::lean_dec_ref(v_m_4636_);
    v_r_4639_ = crate::leanh::lean_box((v_res_4638_) as usize);
    return v_r_4639_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1(
    mut v_00_u03b2_4640_: *mut crate::leanh::LeanObject,
    mut v_m_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_b_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1___redArg(v_m_4641_, v_a_4642_, v_b_4643_);
    return v___x_4644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(
    mut v_00_u03b2_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
    mut v_x_4647_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4648_: u8 = 0;
    v___x_4648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_4646_, v_x_4647_);
    return v___x_4648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___boxed(
    mut v_00_u03b2_4649_: *mut crate::leanh::LeanObject,
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_x_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4652_: u8 = 0;
    let mut v_r_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0(v_00_u03b2_4649_, v_a_4650_, v_x_4651_);
    crate::leanh::lean_dec(v_x_4651_);
    crate::leanh::lean_dec(v_a_4650_);
    v_r_4653_ = crate::leanh::lean_box((v_res_4652_) as usize);
    return v_r_4653_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2(
    mut v_00_u03b2_4654_: *mut crate::leanh::LeanObject,
    mut v_data_4655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4656_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_data_4655_);
    return v___x_4656_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4657_: *mut crate::leanh::LeanObject,
    mut v_i_4658_: *mut crate::leanh::LeanObject,
    mut v_source_4659_: *mut crate::leanh::LeanObject,
    mut v_target_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3___redArg(v_i_4658_, v_source_4659_, v_target_4660_);
    return v___x_4661_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_4662_: *mut crate::leanh::LeanObject,
    mut v_x_4663_: *mut crate::leanh::LeanObject,
    mut v_x_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2_spec__3_spec__4___redArg(v_x_4663_, v_x_4664_);
    return v___x_4665_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(
    mut v_as_4666_: *mut crate::leanh::LeanObject,
    mut v_i_4667_: usize,
    mut v_stop_4668_: usize,
    mut v_b_4669_: u8,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4673_: u8 = 0;
    let mut v___x_4674_: usize = 0;
    let mut v___x_4675_: usize = 0;
    let mut v___y_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4681_: u8 = 0;
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: u8 = 0;
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4681_ = lean_usize_dec_eq(v_i_4667_, v_stop_4668_);
                if v___x_4681_ == 0 {
                    v___x_4682_ = lean_array_uget_borrowed(v_as_4666_, v_i_4667_);
                    crate::leanh::lean_inc(v___x_4682_);
                    v___x_4683_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_4682_, v___x_4681_, v___y_4670_);
                    if crate::leanh::lean_obj_tag(v___x_4683_) == 0 {
                        v_a_4684_ = crate::leanh::lean_ctor_get(v___x_4683_, 0);
                        crate::leanh::lean_inc(v_a_4684_);
                        v___x_4685_ = (crate::leanh::lean_unbox(v_a_4684_) as u8);
                        crate::leanh::lean_dec(v_a_4684_);
                        if v___x_4685_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4683_, 1);
                            v_a_4673_ = v_b_4669_;
                            state = 1;
                            continue;
                        } else {
                            v___y_4678_ = v___x_4683_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_4678_ = v___x_4683_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4686_ = crate::leanh::lean_box((v_b_4669_) as usize);
                    v___x_4687_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4687_, 0, v___x_4686_);
                    return v___x_4687_;
                }
            }
            1 => {
                v___x_4674_ = 1usize;
                v___x_4675_ = lean_usize_add(v_i_4667_, v___x_4674_);
                v_i_4667_ = v___x_4675_;
                v_b_4669_ = v_a_4673_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4678_) == 0 {
                    v_a_4679_ = crate::leanh::lean_ctor_get(v___y_4678_, 0);
                    crate::leanh::lean_inc(v_a_4679_);
                    crate::leanh::lean_dec_ref_known(v___y_4678_, 1);
                    v___x_4680_ = (crate::leanh::lean_unbox(v_a_4679_) as u8);
                    crate::leanh::lean_dec(v_a_4679_);
                    v_a_4673_ = v___x_4680_;
                    state = 1;
                    continue;
                } else {
                    return v___y_4678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg___boxed(
    mut v_as_4688_: *mut crate::leanh::LeanObject,
    mut v_i_4689_: *mut crate::leanh::LeanObject,
    mut v_stop_4690_: *mut crate::leanh::LeanObject,
    mut v_b_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4694_: usize = 0;
    let mut v_stop_boxed_4695_: usize = 0;
    let mut v_b_boxed_4696_: u8 = 0;
    let mut v_res_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4694_ = crate::leanh::lean_unbox_usize(v_i_4689_);
    crate::leanh::lean_dec(v_i_4689_);
    v_stop_boxed_4695_ = crate::leanh::lean_unbox_usize(v_stop_4690_);
    crate::leanh::lean_dec(v_stop_4690_);
    v_b_boxed_4696_ = (crate::leanh::lean_unbox(v_b_4691_) as u8);
    v_res_4697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_4688_, v_i_boxed_4694_, v_stop_boxed_4695_, v_b_boxed_4696_, v___y_4692_);
    crate::leanh::lean_dec(v___y_4692_);
    crate::leanh::lean_dec_ref(v_as_4688_);
    return v_res_4697_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(
    mut v_upperBound_4698_: *mut crate::leanh::LeanObject,
    mut v_args_4699_: *mut crate::leanh::LeanObject,
    mut v_val_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
    mut v_b_4702_: u8,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4706_: u8 = 0;
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: u8 = 0;
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4716_: u8 = 0;
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: u8 = 0;
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_4724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4710_ = lean_nat_dec_lt(v_a_4701_, v_upperBound_4698_);
                if v___x_4710_ == 0 {
                    crate::leanh::lean_dec(v_a_4701_);
                    v___x_4711_ = crate::leanh::lean_box((v_b_4702_) as usize);
                    v___x_4712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4712_, 0, v___x_4711_);
                    return v___x_4712_;
                } else {
                    v_params_4713_ = crate::leanh::lean_ctor_get(v_val_4700_, 3);
                    v___x_4714_ = lean_array_fget_borrowed(v_args_4699_, v_a_4701_);
                    v___x_4721_ = lean_array_get_size(v_params_4713_);
                    v___x_4722_ = lean_nat_dec_lt(v_a_4701_, v___x_4721_);
                    if v___x_4722_ == 0 {
                        v___y_4716_ = v___x_4722_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4723_ = lean_array_fget_borrowed(v_params_4713_, v_a_4701_);
                        v_borrow_4724_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_4723_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_4716_ = v_borrow_4724_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4707_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4708_ = lean_nat_add(v_a_4701_, v___x_4707_);
                crate::leanh::lean_dec(v_a_4701_);
                v_a_4701_ = v___x_4708_;
                v_b_4702_ = v_a_4706_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_4714_);
                v___x_4717_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_4714_, v___y_4716_, v___y_4703_);
                if crate::leanh::lean_obj_tag(v___x_4717_) == 0 {
                    v_a_4718_ = crate::leanh::lean_ctor_get(v___x_4717_, 0);
                    crate::leanh::lean_inc(v_a_4718_);
                    crate::leanh::lean_dec_ref_known(v___x_4717_, 1);
                    v___x_4719_ = (crate::leanh::lean_unbox(v_a_4718_) as u8);
                    if v___x_4719_ == 0 {
                        crate::leanh::lean_dec(v_a_4718_);
                        v_a_4706_ = v_b_4702_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4720_ = (crate::leanh::lean_unbox(v_a_4718_) as u8);
                        crate::leanh::lean_dec(v_a_4718_);
                        v_a_4706_ = v___x_4720_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4701_);
                    return v___x_4717_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg___boxed(
    mut v_upperBound_4725_: *mut crate::leanh::LeanObject,
    mut v_args_4726_: *mut crate::leanh::LeanObject,
    mut v_val_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
    mut v_b_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_4732_: u8 = 0;
    let mut v_res_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4732_ = (crate::leanh::lean_unbox(v_b_4729_) as u8);
    v_res_4733_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_4725_, v_args_4726_, v_val_4727_, v_a_4728_, v_b_boxed_4732_, v___y_4730_);
    crate::leanh::lean_dec(v___y_4730_);
    crate::leanh::lean_dec_ref(v_val_4727_);
    crate::leanh::lean_dec_ref(v_args_4726_);
    crate::leanh::lean_dec(v_upperBound_4725_);
    return v_res_4733_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(
    mut v_as_4734_: *mut crate::leanh::LeanObject,
    mut v_i_4735_: usize,
    mut v_stop_4736_: usize,
    mut v_b_4737_: u8,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4741_: u8 = 0;
    let mut v___x_4742_: usize = 0;
    let mut v___x_4743_: usize = 0;
    let mut v___y_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: u8 = 0;
    let mut v___x_4749_: u8 = 0;
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: u8 = 0;
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4749_ = lean_usize_dec_eq(v_i_4735_, v_stop_4736_);
                if v___x_4749_ == 0 {
                    v___x_4750_ = lean_array_uget_borrowed(v_as_4734_, v_i_4735_);
                    crate::leanh::lean_inc(v___x_4750_);
                    v___x_4751_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_4750_, v___x_4749_, v___y_4738_);
                    if crate::leanh::lean_obj_tag(v___x_4751_) == 0 {
                        v_a_4752_ = crate::leanh::lean_ctor_get(v___x_4751_, 0);
                        crate::leanh::lean_inc(v_a_4752_);
                        v___x_4753_ = (crate::leanh::lean_unbox(v_a_4752_) as u8);
                        crate::leanh::lean_dec(v_a_4752_);
                        if v___x_4753_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4751_, 1);
                            v_a_4741_ = v_b_4737_;
                            state = 1;
                            continue;
                        } else {
                            v___y_4746_ = v___x_4751_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_4746_ = v___x_4751_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4754_ = crate::leanh::lean_box((v_b_4737_) as usize);
                    v___x_4755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4755_, 0, v___x_4754_);
                    return v___x_4755_;
                }
            }
            1 => {
                v___x_4742_ = 1usize;
                v___x_4743_ = lean_usize_add(v_i_4735_, v___x_4742_);
                v_i_4735_ = v___x_4743_;
                v_b_4737_ = v_a_4741_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4746_) == 0 {
                    v_a_4747_ = crate::leanh::lean_ctor_get(v___y_4746_, 0);
                    crate::leanh::lean_inc(v_a_4747_);
                    crate::leanh::lean_dec_ref_known(v___y_4746_, 1);
                    v___x_4748_ = (crate::leanh::lean_unbox(v_a_4747_) as u8);
                    crate::leanh::lean_dec(v_a_4747_);
                    v_a_4741_ = v___x_4748_;
                    state = 1;
                    continue;
                } else {
                    return v___y_4746_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg___boxed(
    mut v_as_4756_: *mut crate::leanh::LeanObject,
    mut v_i_4757_: *mut crate::leanh::LeanObject,
    mut v_stop_4758_: *mut crate::leanh::LeanObject,
    mut v_b_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4762_: usize = 0;
    let mut v_stop_boxed_4763_: usize = 0;
    let mut v_b_boxed_4764_: u8 = 0;
    let mut v_res_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4762_ = crate::leanh::lean_unbox_usize(v_i_4757_);
    crate::leanh::lean_dec(v_i_4757_);
    v_stop_boxed_4763_ = crate::leanh::lean_unbox_usize(v_stop_4758_);
    crate::leanh::lean_dec(v_stop_4758_);
    v_b_boxed_4764_ = (crate::leanh::lean_unbox(v_b_4759_) as u8);
    v_res_4765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_4756_, v_i_boxed_4762_, v_stop_boxed_4763_, v_b_boxed_4764_, v___y_4760_);
    crate::leanh::lean_dec(v___y_4760_);
    crate::leanh::lean_dec_ref(v_as_4756_);
    return v_res_4765_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(
    mut v_value_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
    mut v_a_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
    mut v_a_4771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4775_: u8 = 0;
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4781_: u8 = 0;
    let mut v_unused_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: u8 = 0;
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4797_: u8 = 0;
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: u8 = 0;
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: u8 = 0;
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: usize = 0;
    let mut v___x_4814_: usize = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: u8 = 0;
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4821_: u8 = 0;
    let mut v_a_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4829_: u8 = 0;
    let mut v_fvarId_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: u8 = 0;
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: u8 = 0;
    let mut v___x_4839_: u8 = 0;
    let mut v___x_4840_: usize = 0;
    let mut v___x_4841_: usize = 0;
    let mut v___x_4842_: u8 = 0;
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: usize = 0;
    let mut v___x_4845_: usize = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_value_4766_) {
                0 => {
                    v_isSharedCheck_4781_ = (!crate::leanh::lean_is_exclusive(v_value_4766_)) as u8;
                    if v_isSharedCheck_4781_ == 0 {
                        v_unused_4782_ = crate::leanh::lean_ctor_get(v_value_4766_, 0);
                        crate::leanh::lean_dec(v_unused_4782_);
                        v___x_4774_ = v_value_4766_;
                        v_isShared_4775_ = v_isSharedCheck_4781_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_value_4766_);
                        v___x_4774_ = crate::leanh::lean_box(0);
                        v_isShared_4775_ = v_isSharedCheck_4781_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4783_ = 0;
                    v___x_4784_ = crate::leanh::lean_box((v___x_4783_) as usize);
                    v___x_4785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4785_, 0, v___x_4784_);
                    return v___x_4785_;
                }
                2 => {
                    v_struct_4786_ = crate::leanh::lean_ctor_get(v_value_4766_, 2);
                    crate::leanh::lean_inc(v_struct_4786_);
                    crate::leanh::lean_dec_ref_known(v_value_4766_, 3);
                    v___x_4787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4787_, 0, v_struct_4786_);
                    v___x_4788_ = 1;
                    v___x_4789_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_4787_, v___x_4788_, v_a_4767_);
                    return v___x_4789_;
                }
                3 => {
                    v_declName_4790_ = crate::leanh::lean_ctor_get(v_value_4766_, 0);
                    crate::leanh::lean_inc(v_declName_4790_);
                    v_args_4791_ = crate::leanh::lean_ctor_get(v_value_4766_, 2);
                    crate::leanh::lean_inc_ref(v_args_4791_);
                    crate::leanh::lean_dec_ref_known(v_value_4766_, 3);
                    v___x_4792_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(
                        v_declName_4790_,
                        v_a_4771_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4792_) == 0 {
                        v_a_4793_ = crate::leanh::lean_ctor_get(v___x_4792_, 0);
                        v_isSharedCheck_4821_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4792_)) as u8;
                        if v_isSharedCheck_4821_ == 0 {
                            v___x_4795_ = v___x_4792_;
                            v_isShared_4796_ = v_isSharedCheck_4821_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4793_);
                            crate::leanh::lean_dec(v___x_4792_);
                            v___x_4795_ = crate::leanh::lean_box(0);
                            v_isShared_4796_ = v_isSharedCheck_4821_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_4791_);
                        v_a_4822_ = crate::leanh::lean_ctor_get(v___x_4792_, 0);
                        v_isSharedCheck_4829_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4792_)) as u8;
                        if v_isSharedCheck_4829_ == 0 {
                            v___x_4824_ = v___x_4792_;
                            v_isShared_4825_ = v_isSharedCheck_4829_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4822_);
                            crate::leanh::lean_dec(v___x_4792_);
                            v___x_4824_ = crate::leanh::lean_box(0);
                            v_isShared_4825_ = v_isSharedCheck_4829_;
                            state = 6;
                            continue;
                        }
                    }
                }
                _ => {
                    v_fvarId_4830_ = crate::leanh::lean_ctor_get(v_value_4766_, 0);
                    crate::leanh::lean_inc(v_fvarId_4830_);
                    v_args_4831_ = crate::leanh::lean_ctor_get(v_value_4766_, 1);
                    crate::leanh::lean_inc_ref(v_args_4831_);
                    crate::leanh::lean_dec_ref_known(v_value_4766_, 2);
                    v___x_4832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4832_, 0, v_fvarId_4830_);
                    v___x_4833_ = 0;
                    v___x_4834_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg___redArg(v___x_4832_, v___x_4833_, v_a_4767_);
                    v_a_4835_ = crate::leanh::lean_ctor_get(v___x_4834_, 0);
                    crate::leanh::lean_inc(v_a_4835_);
                    v___x_4836_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4837_ = lean_array_get_size(v_args_4831_);
                    v___x_4838_ = lean_nat_dec_lt(v___x_4836_, v___x_4837_);
                    if v___x_4838_ == 0 {
                        crate::leanh::lean_dec(v_a_4835_);
                        crate::leanh::lean_dec_ref(v_args_4831_);
                        return v___x_4834_;
                    } else {
                        v___x_4839_ = lean_nat_dec_le(v___x_4837_, v___x_4837_);
                        if v___x_4839_ == 0 {
                            if v___x_4838_ == 0 {
                                crate::leanh::lean_dec(v_a_4835_);
                                crate::leanh::lean_dec_ref(v_args_4831_);
                                return v___x_4834_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4834_);
                                v___x_4840_ = 0usize;
                                v___x_4841_ = lean_usize_of_nat(v___x_4837_);
                                v___x_4842_ = (crate::leanh::lean_unbox(v_a_4835_) as u8);
                                crate::leanh::lean_dec(v_a_4835_);
                                v___x_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_4831_, v___x_4840_, v___x_4841_, v___x_4842_, v_a_4767_);
                                crate::leanh::lean_dec_ref(v_args_4831_);
                                return v___x_4843_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4834_);
                            v___x_4844_ = 0usize;
                            v___x_4845_ = lean_usize_of_nat(v___x_4837_);
                            v___x_4846_ = (crate::leanh::lean_unbox(v_a_4835_) as u8);
                            crate::leanh::lean_dec(v_a_4835_);
                            v___x_4847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_args_4831_, v___x_4844_, v___x_4845_, v___x_4846_, v_a_4767_);
                            crate::leanh::lean_dec_ref(v_args_4831_);
                            return v___x_4847_;
                        }
                    }
                }
            },
            1 => {
                v___x_4776_ = 0;
                v___x_4777_ = crate::leanh::lean_box((v___x_4776_) as usize);
                if v_isShared_4775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4774_, 0, v___x_4777_);
                    v___x_4779_ = v___x_4774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4780_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
                    v___x_4779_ = v_reuseFailAlloc_4780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4779_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_4793_) == 0 {
                    v___x_4797_ = 0;
                    v___x_4798_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4799_ = lean_array_get_size(v_args_4791_);
                    v___x_4800_ = lean_nat_dec_lt(v___x_4798_, v___x_4799_);
                    if v___x_4800_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_4791_);
                        v___x_4801_ = crate::leanh::lean_box((v___x_4797_) as usize);
                        if v_isShared_4796_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4795_, 0, v___x_4801_);
                            v___x_4803_ = v___x_4795_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4804_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4801_);
                            v___x_4803_ = v_reuseFailAlloc_4804_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_4805_ = lean_nat_dec_le(v___x_4799_, v___x_4799_);
                        if v___x_4805_ == 0 {
                            if v___x_4800_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_4791_);
                                v___x_4806_ = crate::leanh::lean_box((v___x_4797_) as usize);
                                if v_isShared_4796_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4795_, 0, v___x_4806_);
                                    v___x_4808_ = v___x_4795_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4809_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4809_,
                                        0,
                                        v___x_4806_,
                                    );
                                    v___x_4808_ = v_reuseFailAlloc_4809_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_4795_);
                                v___x_4810_ = 0usize;
                                v___x_4811_ = lean_usize_of_nat(v___x_4799_);
                                v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_4791_, v___x_4810_, v___x_4811_, v___x_4797_, v_a_4767_);
                                crate::leanh::lean_dec_ref(v_args_4791_);
                                return v___x_4812_;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4795_);
                            v___x_4813_ = 0usize;
                            v___x_4814_ = lean_usize_of_nat(v___x_4799_);
                            v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_args_4791_, v___x_4813_, v___x_4814_, v___x_4797_, v_a_4767_);
                            crate::leanh::lean_dec_ref(v_args_4791_);
                            return v___x_4815_;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4795_);
                    v_val_4816_ = crate::leanh::lean_ctor_get(v_a_4793_, 0);
                    crate::leanh::lean_inc(v_val_4816_);
                    crate::leanh::lean_dec_ref_known(v_a_4793_, 1);
                    v___x_4817_ = lean_array_get_size(v_args_4791_);
                    v___x_4818_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4819_ = 0;
                    v___x_4820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v___x_4817_, v_args_4791_, v_val_4816_, v___x_4818_, v___x_4819_, v_a_4767_);
                    crate::leanh::lean_dec(v_val_4816_);
                    crate::leanh::lean_dec_ref(v_args_4791_);
                    return v___x_4820_;
                }
            }
            4 => {
                return v___x_4803_;
            }
            5 => {
                return v___x_4808_;
            }
            6 => {
                if v_isShared_4825_ == 0 {
                    v___x_4827_ = v___x_4824_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
                    v___x_4827_ = v_reuseFailAlloc_4828_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg___boxed(
    mut v_value_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
    mut v_a_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4855_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_4848_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_, v_a_4853_);
    crate::leanh::lean_dec(v_a_4853_);
    crate::leanh::lean_dec_ref(v_a_4852_);
    crate::leanh::lean_dec(v_a_4851_);
    crate::leanh::lean_dec_ref(v_a_4850_);
    crate::leanh::lean_dec(v_a_4849_);
    return v_res_4855_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(
    mut v_env_4856_: *mut crate::leanh::LeanObject,
    mut v_value_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
    return v___x_4864_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___boxed(
    mut v_env_4865_: *mut crate::leanh::LeanObject,
    mut v_value_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
    mut v_a_4870_: *mut crate::leanh::LeanObject,
    mut v_a_4871_: *mut crate::leanh::LeanObject,
    mut v_a_4872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4873_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue(v_env_4865_, v_value_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
    crate::leanh::lean_dec(v_a_4871_);
    crate::leanh::lean_dec_ref(v_a_4870_);
    crate::leanh::lean_dec(v_a_4869_);
    crate::leanh::lean_dec_ref(v_a_4868_);
    crate::leanh::lean_dec(v_a_4867_);
    crate::leanh::lean_dec_ref(v_env_4865_);
    return v_res_4873_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(
    mut v_as_4874_: *mut crate::leanh::LeanObject,
    mut v_i_4875_: usize,
    mut v_stop_4876_: usize,
    mut v_b_4877_: u8,
    mut v___y_4878_: *mut crate::leanh::LeanObject,
    mut v___y_4879_: *mut crate::leanh::LeanObject,
    mut v___y_4880_: *mut crate::leanh::LeanObject,
    mut v___y_4881_: *mut crate::leanh::LeanObject,
    mut v___y_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___redArg(v_as_4874_, v_i_4875_, v_stop_4876_, v_b_4877_, v___y_4878_);
    return v___x_4884_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0___boxed(
    mut v_as_4885_: *mut crate::leanh::LeanObject,
    mut v_i_4886_: *mut crate::leanh::LeanObject,
    mut v_stop_4887_: *mut crate::leanh::LeanObject,
    mut v_b_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4895_: usize = 0;
    let mut v_stop_boxed_4896_: usize = 0;
    let mut v_b_boxed_4897_: u8 = 0;
    let mut v_res_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4895_ = crate::leanh::lean_unbox_usize(v_i_4886_);
    crate::leanh::lean_dec(v_i_4886_);
    v_stop_boxed_4896_ = crate::leanh::lean_unbox_usize(v_stop_4887_);
    crate::leanh::lean_dec(v_stop_4887_);
    v_b_boxed_4897_ = (crate::leanh::lean_unbox(v_b_4888_) as u8);
    v_res_4898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__0(v_as_4885_, v_i_boxed_4895_, v_stop_boxed_4896_, v_b_boxed_4897_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
    crate::leanh::lean_dec(v___y_4893_);
    crate::leanh::lean_dec_ref(v___y_4892_);
    crate::leanh::lean_dec(v___y_4891_);
    crate::leanh::lean_dec_ref(v___y_4890_);
    crate::leanh::lean_dec(v___y_4889_);
    crate::leanh::lean_dec_ref(v_as_4885_);
    return v_res_4898_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(
    mut v_upperBound_4899_: *mut crate::leanh::LeanObject,
    mut v_args_4900_: *mut crate::leanh::LeanObject,
    mut v_val_4901_: *mut crate::leanh::LeanObject,
    mut v_inst_4902_: *mut crate::leanh::LeanObject,
    mut v_R_4903_: *mut crate::leanh::LeanObject,
    mut v_a_4904_: *mut crate::leanh::LeanObject,
    mut v_b_4905_: u8,
    mut v_c_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4913_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___redArg(v_upperBound_4899_, v_args_4900_, v_val_4901_, v_a_4904_, v_b_4905_, v___y_4907_);
    return v___x_4913_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1___boxed(
    mut v_upperBound_4914_: *mut crate::leanh::LeanObject,
    mut v_args_4915_: *mut crate::leanh::LeanObject,
    mut v_val_4916_: *mut crate::leanh::LeanObject,
    mut v_inst_4917_: *mut crate::leanh::LeanObject,
    mut v_R_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_b_4920_: *mut crate::leanh::LeanObject,
    mut v_c_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
    mut v___y_4924_: *mut crate::leanh::LeanObject,
    mut v___y_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_4928_: u8 = 0;
    let mut v_res_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4928_ = (crate::leanh::lean_unbox(v_b_4920_) as u8);
    v_res_4929_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__1(v_upperBound_4914_, v_args_4915_, v_val_4916_, v_inst_4917_, v_R_4918_, v_a_4919_, v_b_boxed_4928_, v_c_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
    crate::leanh::lean_dec(v___y_4926_);
    crate::leanh::lean_dec_ref(v___y_4925_);
    crate::leanh::lean_dec(v___y_4924_);
    crate::leanh::lean_dec_ref(v___y_4923_);
    crate::leanh::lean_dec(v___y_4922_);
    crate::leanh::lean_dec_ref(v_val_4916_);
    crate::leanh::lean_dec_ref(v_args_4915_);
    crate::leanh::lean_dec(v_upperBound_4914_);
    return v_res_4929_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(
    mut v_as_4930_: *mut crate::leanh::LeanObject,
    mut v_i_4931_: usize,
    mut v_stop_4932_: usize,
    mut v_b_4933_: u8,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___redArg(v_as_4930_, v_i_4931_, v_stop_4932_, v_b_4933_, v___y_4934_);
    return v___x_4940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2___boxed(
    mut v_as_4941_: *mut crate::leanh::LeanObject,
    mut v_i_4942_: *mut crate::leanh::LeanObject,
    mut v_stop_4943_: *mut crate::leanh::LeanObject,
    mut v_b_4944_: *mut crate::leanh::LeanObject,
    mut v___y_4945_: *mut crate::leanh::LeanObject,
    mut v___y_4946_: *mut crate::leanh::LeanObject,
    mut v___y_4947_: *mut crate::leanh::LeanObject,
    mut v___y_4948_: *mut crate::leanh::LeanObject,
    mut v___y_4949_: *mut crate::leanh::LeanObject,
    mut v___y_4950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4951_: usize = 0;
    let mut v_stop_boxed_4952_: usize = 0;
    let mut v_b_boxed_4953_: u8 = 0;
    let mut v_res_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4951_ = crate::leanh::lean_unbox_usize(v_i_4942_);
    crate::leanh::lean_dec(v_i_4942_);
    v_stop_boxed_4952_ = crate::leanh::lean_unbox_usize(v_stop_4943_);
    crate::leanh::lean_dec(v_stop_4943_);
    v_b_boxed_4953_ = (crate::leanh::lean_unbox(v_b_4944_) as u8);
    v_res_4954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue_spec__2(v_as_4941_, v_i_boxed_4951_, v_stop_boxed_4952_, v_b_boxed_4953_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
    crate::leanh::lean_dec(v___y_4949_);
    crate::leanh::lean_dec_ref(v___y_4948_);
    crate::leanh::lean_dec(v___y_4947_);
    crate::leanh::lean_dec_ref(v___y_4946_);
    crate::leanh::lean_dec(v___y_4945_);
    crate::leanh::lean_dec_ref(v_as_4941_);
    return v_res_4954_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(
    mut v_value_4955_: *mut crate::leanh::LeanObject,
    mut v_a_4956_: *mut crate::leanh::LeanObject,
    mut v_a_4957_: *mut crate::leanh::LeanObject,
    mut v_a_4958_: *mut crate::leanh::LeanObject,
    mut v_a_4959_: *mut crate::leanh::LeanObject,
    mut v_a_4960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_value_4955_) == 0 {
        let mut v_decl_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_decl_4962_ = crate::leanh::lean_ctor_get(v_value_4955_, 0);
        crate::leanh::lean_inc_ref(v_decl_4962_);
        crate::leanh::lean_dec_ref_known(v_value_4955_, 1);
        v_value_4963_ = crate::leanh::lean_ctor_get(v_decl_4962_, 3);
        crate::leanh::lean_inc(v_value_4963_);
        crate::leanh::lean_dec_ref(v_decl_4962_);
        v___x_4964_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitLetValue___redArg(v_value_4963_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
        return v___x_4964_;
    } else {
        let mut v___x_4965_: u8 = 0;
        let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_value_4955_);
        v___x_4965_ = 0;
        v___x_4966_ = crate::leanh::lean_box((v___x_4965_) as usize);
        v___x_4967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4967_, 0, v___x_4966_);
        return v___x_4967_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg___boxed(
    mut v_value_4968_: *mut crate::leanh::LeanObject,
    mut v_a_4969_: *mut crate::leanh::LeanObject,
    mut v_a_4970_: *mut crate::leanh::LeanObject,
    mut v_a_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
    mut v_a_4973_: *mut crate::leanh::LeanObject,
    mut v_a_4974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4975_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_);
    crate::leanh::lean_dec(v_a_4973_);
    crate::leanh::lean_dec_ref(v_a_4972_);
    crate::leanh::lean_dec(v_a_4971_);
    crate::leanh::lean_dec_ref(v_a_4970_);
    crate::leanh::lean_dec(v_a_4969_);
    return v_res_4975_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(
    mut v_env_4976_: *mut crate::leanh::LeanObject,
    mut v_value_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
    mut v_a_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
    mut v_a_4981_: *mut crate::leanh::LeanObject,
    mut v_a_4982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4984_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_value_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_);
    return v___x_4984_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___boxed(
    mut v_env_4985_: *mut crate::leanh::LeanObject,
    mut v_value_4986_: *mut crate::leanh::LeanObject,
    mut v_a_4987_: *mut crate::leanh::LeanObject,
    mut v_a_4988_: *mut crate::leanh::LeanObject,
    mut v_a_4989_: *mut crate::leanh::LeanObject,
    mut v_a_4990_: *mut crate::leanh::LeanObject,
    mut v_a_4991_: *mut crate::leanh::LeanObject,
    mut v_a_4992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4993_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl(v_env_4985_, v_value_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_);
    crate::leanh::lean_dec(v_a_4991_);
    crate::leanh::lean_dec_ref(v_a_4990_);
    crate::leanh::lean_dec(v_a_4989_);
    crate::leanh::lean_dec_ref(v_a_4988_);
    crate::leanh::lean_dec(v_a_4987_);
    crate::leanh::lean_dec_ref(v_env_4985_);
    return v_res_4993_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(
    mut v_a_4994_: *mut crate::leanh::LeanObject,
    mut v_b_4995_: *mut crate::leanh::LeanObject,
    mut v_x_4996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5002_: u8 = 0;
    let mut v___x_5003_: u8 = 0;
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4996_) == 0 {
                    crate::leanh::lean_dec(v_b_4995_);
                    crate::leanh::lean_dec(v_a_4994_);
                    return v_x_4996_;
                } else {
                    v_key_4997_ = crate::leanh::lean_ctor_get(v_x_4996_, 0);
                    v_value_4998_ = crate::leanh::lean_ctor_get(v_x_4996_, 1);
                    v_tail_4999_ = crate::leanh::lean_ctor_get(v_x_4996_, 2);
                    v_isSharedCheck_5011_ = (!crate::leanh::lean_is_exclusive(v_x_4996_)) as u8;
                    if v_isSharedCheck_5011_ == 0 {
                        v___x_5001_ = v_x_4996_;
                        v_isShared_5002_ = v_isSharedCheck_5011_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4999_);
                        crate::leanh::lean_inc(v_value_4998_);
                        crate::leanh::lean_inc(v_key_4997_);
                        crate::leanh::lean_dec(v_x_4996_);
                        v___x_5001_ = crate::leanh::lean_box(0);
                        v_isShared_5002_ = v_isSharedCheck_5011_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5003_ = l_Lean_instBEqFVarId_beq(v_key_4997_, v_a_4994_);
                if v___x_5003_ == 0 {
                    v___x_5004_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_4994_, v_b_4995_, v_tail_4999_);
                    if v_isShared_5002_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5001_, 2, v___x_5004_);
                        v___x_5006_ = v___x_5001_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5007_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_key_4997_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 1, v_value_4998_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 2, v___x_5004_);
                        v___x_5006_ = v_reuseFailAlloc_5007_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4998_);
                    crate::leanh::lean_dec(v_key_4997_);
                    if v_isShared_5002_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5001_, 1, v_b_4995_);
                        crate::leanh::lean_ctor_set(v___x_5001_, 0, v_a_4994_);
                        v___x_5009_ = v___x_5001_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5010_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_4994_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_b_4995_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 2, v_tail_4999_);
                        v___x_5009_ = v_reuseFailAlloc_5010_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5006_;
            }
            3 => {
                return v___x_5009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(
    mut v_m_5012_: *mut crate::leanh::LeanObject,
    mut v_a_5013_: *mut crate::leanh::LeanObject,
    mut v_b_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: u64 = 0;
    let mut v___x_5022_: u64 = 0;
    let mut v___x_5023_: u64 = 0;
    let mut v_fold_5024_: u64 = 0;
    let mut v___x_5025_: u64 = 0;
    let mut v___x_5026_: u64 = 0;
    let mut v___x_5027_: u64 = 0;
    let mut v___x_5028_: usize = 0;
    let mut v___x_5029_: usize = 0;
    let mut v___x_5030_: usize = 0;
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: usize = 0;
    let mut v_bkt_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: u8 = 0;
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: u8 = 0;
    let mut v_val_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5015_ = crate::leanh::lean_ctor_get(v_m_5012_, 0);
                v_buckets_5016_ = crate::leanh::lean_ctor_get(v_m_5012_, 1);
                v_isSharedCheck_5059_ = (!crate::leanh::lean_is_exclusive(v_m_5012_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v___x_5018_ = v_m_5012_;
                    v_isShared_5019_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_5016_);
                    crate::leanh::lean_inc(v_size_5015_);
                    crate::leanh::lean_dec(v_m_5012_);
                    v___x_5018_ = crate::leanh::lean_box(0);
                    v_isShared_5019_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5020_ = lean_array_get_size(v_buckets_5016_);
                v___x_5021_ = l_Lean_instHashableFVarId_hash(v_a_5013_);
                v___x_5022_ = 32u64;
                v___x_5023_ = lean_uint64_shift_right(v___x_5021_, v___x_5022_);
                v_fold_5024_ = lean_uint64_xor(v___x_5021_, v___x_5023_);
                v___x_5025_ = 16u64;
                v___x_5026_ = lean_uint64_shift_right(v_fold_5024_, v___x_5025_);
                v___x_5027_ = lean_uint64_xor(v_fold_5024_, v___x_5026_);
                v___x_5028_ = lean_uint64_to_usize(v___x_5027_);
                v___x_5029_ = lean_usize_of_nat(v___x_5020_);
                v___x_5030_ = 1usize;
                v___x_5031_ = lean_usize_sub(v___x_5029_, v___x_5030_);
                v___x_5032_ = lean_usize_land(v___x_5028_, v___x_5031_);
                v_bkt_5033_ = lean_array_uget_borrowed(v_buckets_5016_, v___x_5032_);
                v___x_5034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0_spec__0___redArg(v_a_5013_, v_bkt_5033_);
                if v___x_5034_ == 0 {
                    v___x_5035_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5036_ = lean_nat_add(v_size_5015_, v___x_5035_);
                    crate::leanh::lean_dec(v_size_5015_);
                    crate::leanh::lean_inc(v_bkt_5033_);
                    v___x_5037_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5037_, 0, v_a_5013_);
                    crate::leanh::lean_ctor_set(v___x_5037_, 1, v_b_5014_);
                    crate::leanh::lean_ctor_set(v___x_5037_, 2, v_bkt_5033_);
                    v_buckets_x27_5038_ =
                        lean_array_uset(v_buckets_5016_, v___x_5032_, v___x_5037_);
                    v___x_5039_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5040_ = lean_nat_mul(v_size_x27_5036_, v___x_5039_);
                    v___x_5041_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5042_ = lean_nat_div(v___x_5040_, v___x_5041_);
                    crate::leanh::lean_dec(v___x_5040_);
                    v___x_5043_ = lean_array_get_size(v_buckets_x27_5038_);
                    v___x_5044_ = lean_nat_dec_le(v___x_5042_, v___x_5043_);
                    crate::leanh::lean_dec(v___x_5042_);
                    if v___x_5044_ == 0 {
                        v_val_5045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__1_spec__2___redArg(v_buckets_x27_5038_);
                        if v_isShared_5019_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5018_, 1, v_val_5045_);
                            crate::leanh::lean_ctor_set(v___x_5018_, 0, v_size_x27_5036_);
                            v___x_5047_ = v___x_5018_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5048_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5048_,
                                0,
                                v_size_x27_5036_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5048_, 1, v_val_5045_);
                            v___x_5047_ = v_reuseFailAlloc_5048_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_5019_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5018_, 1, v_buckets_x27_5038_);
                            crate::leanh::lean_ctor_set(v___x_5018_, 0, v_size_x27_5036_);
                            v___x_5050_ = v___x_5018_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5051_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5051_,
                                0,
                                v_size_x27_5036_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5051_,
                                1,
                                v_buckets_x27_5038_,
                            );
                            v___x_5050_ = v_reuseFailAlloc_5051_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_5033_);
                    v___x_5052_ = crate::leanh::lean_box(0);
                    v_buckets_x27_5053_ =
                        lean_array_uset(v_buckets_5016_, v___x_5032_, v___x_5052_);
                    v___x_5054_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_5013_, v_b_5014_, v_bkt_5033_);
                    v___x_5055_ = lean_array_uset(v_buckets_x27_5053_, v___x_5032_, v___x_5054_);
                    if v_isShared_5019_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5018_, 1, v___x_5055_);
                        v___x_5057_ = v___x_5018_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_size_5015_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 1, v___x_5055_);
                        v___x_5057_ = v_reuseFailAlloc_5058_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5047_;
            }
            3 => {
                return v___x_5050_;
            }
            4 => {
                return v___x_5057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(
    mut v_a_5060_: *mut crate::leanh::LeanObject,
    mut v_x_5061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: u8 = 0;
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5061_) == 0 {
                    v___x_5062_ = crate::leanh::lean_box(0);
                    return v___x_5062_;
                } else {
                    v_key_5063_ = crate::leanh::lean_ctor_get(v_x_5061_, 0);
                    v_value_5064_ = crate::leanh::lean_ctor_get(v_x_5061_, 1);
                    v_tail_5065_ = crate::leanh::lean_ctor_get(v_x_5061_, 2);
                    v___x_5066_ = l_Lean_instBEqFVarId_beq(v_key_5063_, v_a_5060_);
                    if v___x_5066_ == 0 {
                        v_x_5061_ = v_tail_5065_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5064_);
                        v___x_5068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5068_, 0, v_value_5064_);
                        return v___x_5068_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg___boxed(
    mut v_a_5069_: *mut crate::leanh::LeanObject,
    mut v_x_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_5069_, v_x_5070_);
    crate::leanh::lean_dec(v_x_5070_);
    crate::leanh::lean_dec(v_a_5069_);
    return v_res_5071_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(
    mut v_m_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: u64 = 0;
    let mut v___x_5077_: u64 = 0;
    let mut v___x_5078_: u64 = 0;
    let mut v_fold_5079_: u64 = 0;
    let mut v___x_5080_: u64 = 0;
    let mut v___x_5081_: u64 = 0;
    let mut v___x_5082_: u64 = 0;
    let mut v___x_5083_: usize = 0;
    let mut v___x_5084_: usize = 0;
    let mut v___x_5085_: usize = 0;
    let mut v___x_5086_: usize = 0;
    let mut v___x_5087_: usize = 0;
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5074_ = crate::leanh::lean_ctor_get(v_m_5072_, 1);
    v___x_5075_ = lean_array_get_size(v_buckets_5074_);
    v___x_5076_ = l_Lean_instHashableFVarId_hash(v_a_5073_);
    v___x_5077_ = 32u64;
    v___x_5078_ = lean_uint64_shift_right(v___x_5076_, v___x_5077_);
    v_fold_5079_ = lean_uint64_xor(v___x_5076_, v___x_5078_);
    v___x_5080_ = 16u64;
    v___x_5081_ = lean_uint64_shift_right(v_fold_5079_, v___x_5080_);
    v___x_5082_ = lean_uint64_xor(v_fold_5079_, v___x_5081_);
    v___x_5083_ = lean_uint64_to_usize(v___x_5082_);
    v___x_5084_ = lean_usize_of_nat(v___x_5075_);
    v___x_5085_ = 1usize;
    v___x_5086_ = lean_usize_sub(v___x_5084_, v___x_5085_);
    v___x_5087_ = lean_usize_land(v___x_5083_, v___x_5086_);
    v___x_5088_ = lean_array_uget_borrowed(v_buckets_5074_, v___x_5087_);
    v___x_5089_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_5073_, v___x_5088_);
    return v___x_5089_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg___boxed(
    mut v_m_5090_: *mut crate::leanh::LeanObject,
    mut v_a_5091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5092_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_5090_, v_a_5091_);
    crate::leanh::lean_dec(v_a_5091_);
    crate::leanh::lean_dec_ref(v_m_5090_);
    return v_res_5092_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(
    mut v_plannedDecision_5093_: *mut crate::leanh::LeanObject,
    mut v_var_5094_: *mut crate::leanh::LeanObject,
    mut v_a_5095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5097_ = lean_st_ref_get(v_a_5095_);
                v___x_5098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v___x_5097_, v_var_5094_);
                crate::leanh::lean_dec(v___x_5097_);
                if crate::leanh::lean_obj_tag(v___x_5098_) == 1 {
                    v_val_5099_ = crate::leanh::lean_ctor_get(v___x_5098_, 0);
                    v_isSharedCheck_5123_ = (!crate::leanh::lean_is_exclusive(v___x_5098_)) as u8;
                    if v_isSharedCheck_5123_ == 0 {
                        v___x_5101_ = v___x_5098_;
                        v_isShared_5102_ = v_isSharedCheck_5123_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5099_);
                        crate::leanh::lean_dec(v___x_5098_);
                        v___x_5101_ = crate::leanh::lean_box(0);
                        v_isShared_5102_ = v_isSharedCheck_5123_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5098_);
                    crate::leanh::lean_dec(v_var_5094_);
                    crate::leanh::lean_dec(v_plannedDecision_5093_);
                    v___x_5124_ = crate::leanh::lean_box(0);
                    v___x_5125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5125_, 0, v___x_5124_);
                    return v___x_5125_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_5099_) == 3 {
                    v___x_5103_ = lean_st_ref_take(v_a_5095_);
                    v___x_5104_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_5103_, v_var_5094_, v_plannedDecision_5093_);
                    v___x_5105_ = lean_st_ref_set(v_a_5095_, v___x_5104_);
                    v___x_5106_ = crate::leanh::lean_box(0);
                    if v_isShared_5102_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5101_, 0);
                        crate::leanh::lean_ctor_set(v___x_5101_, 0, v___x_5106_);
                        v___x_5108_ = v___x_5101_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5106_);
                        v___x_5108_ = v_reuseFailAlloc_5109_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5110_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(
                        v_val_5099_,
                        v_plannedDecision_5093_,
                    );
                    crate::leanh::lean_dec(v_plannedDecision_5093_);
                    crate::leanh::lean_dec(v_val_5099_);
                    if v___x_5110_ == 0 {
                        v___x_5111_ = lean_st_ref_take(v_a_5095_);
                        v___x_5112_ = crate::leanh::lean_box(2);
                        v___x_5113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v___x_5111_, v_var_5094_, v___x_5112_);
                        v___x_5114_ = lean_st_ref_set(v_a_5095_, v___x_5113_);
                        v___x_5115_ = crate::leanh::lean_box(0);
                        if v_isShared_5102_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5101_, 0);
                            crate::leanh::lean_ctor_set(v___x_5101_, 0, v___x_5115_);
                            v___x_5117_ = v___x_5101_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5118_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5115_);
                            v___x_5117_ = v_reuseFailAlloc_5118_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_var_5094_);
                        v___x_5119_ = crate::leanh::lean_box(0);
                        if v_isShared_5102_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5101_, 0);
                            crate::leanh::lean_ctor_set(v___x_5101_, 0, v___x_5119_);
                            v___x_5121_ = v___x_5101_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5122_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
                            v___x_5121_ = v_reuseFailAlloc_5122_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5108_;
            }
            3 => {
                return v___x_5117_;
            }
            4 => {
                return v___x_5121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(
    mut v_plannedDecision_5126_: *mut crate::leanh::LeanObject,
    mut v_var_5127_: *mut crate::leanh::LeanObject,
    mut v_a_5128_: *mut crate::leanh::LeanObject,
    mut v_a_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_5126_, v_var_5127_, v_a_5128_);
    crate::leanh::lean_dec(v_a_5128_);
    return v_res_5130_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(
    mut v_plannedDecision_5131_: *mut crate::leanh::LeanObject,
    mut v_var_5132_: *mut crate::leanh::LeanObject,
    mut v_a_5133_: *mut crate::leanh::LeanObject,
    mut v_a_5134_: *mut crate::leanh::LeanObject,
    mut v_a_5135_: *mut crate::leanh::LeanObject,
    mut v_a_5136_: *mut crate::leanh::LeanObject,
    mut v_a_5137_: *mut crate::leanh::LeanObject,
    mut v_a_5138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5140_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(v_plannedDecision_5131_, v_var_5132_, v_a_5133_);
    return v___x_5140_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(
    mut v_plannedDecision_5141_: *mut crate::leanh::LeanObject,
    mut v_var_5142_: *mut crate::leanh::LeanObject,
    mut v_a_5143_: *mut crate::leanh::LeanObject,
    mut v_a_5144_: *mut crate::leanh::LeanObject,
    mut v_a_5145_: *mut crate::leanh::LeanObject,
    mut v_a_5146_: *mut crate::leanh::LeanObject,
    mut v_a_5147_: *mut crate::leanh::LeanObject,
    mut v_a_5148_: *mut crate::leanh::LeanObject,
    mut v_a_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5150_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(v_plannedDecision_5141_, v_var_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_);
    crate::leanh::lean_dec(v_a_5148_);
    crate::leanh::lean_dec_ref(v_a_5147_);
    crate::leanh::lean_dec(v_a_5146_);
    crate::leanh::lean_dec_ref(v_a_5145_);
    crate::leanh::lean_dec(v_a_5144_);
    crate::leanh::lean_dec(v_a_5143_);
    return v_res_5150_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(
    mut v_00_u03b2_5151_: *mut crate::leanh::LeanObject,
    mut v_m_5152_: *mut crate::leanh::LeanObject,
    mut v_a_5153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5154_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_m_5152_, v_a_5153_);
    return v___x_5154_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___boxed(
    mut v_00_u03b2_5155_: *mut crate::leanh::LeanObject,
    mut v_m_5156_: *mut crate::leanh::LeanObject,
    mut v_a_5157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0(v_00_u03b2_5155_, v_m_5156_, v_a_5157_);
    crate::leanh::lean_dec(v_a_5157_);
    crate::leanh::lean_dec_ref(v_m_5156_);
    return v_res_5158_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1(
    mut v_00_u03b2_5159_: *mut crate::leanh::LeanObject,
    mut v_m_5160_: *mut crate::leanh::LeanObject,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
    mut v_b_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_m_5160_, v_a_5161_, v_b_5162_);
    return v___x_5163_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(
    mut v_00_u03b2_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
    mut v_x_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5167_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___redArg(v_a_5165_, v_x_5166_);
    return v___x_5167_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_5168_: *mut crate::leanh::LeanObject,
    mut v_a_5169_: *mut crate::leanh::LeanObject,
    mut v_x_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5171_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0_spec__0(v_00_u03b2_5168_, v_a_5169_, v_x_5170_);
    crate::leanh::lean_dec(v_x_5170_);
    crate::leanh::lean_dec(v_a_5169_);
    return v_res_5171_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2(
    mut v_00_u03b2_5172_: *mut crate::leanh::LeanObject,
    mut v_a_5173_: *mut crate::leanh::LeanObject,
    mut v_b_5174_: *mut crate::leanh::LeanObject,
    mut v_x_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1_spec__2___redArg(v_a_5173_, v_b_5174_, v_x_5175_);
    return v___x_5176_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(
    mut v_alt_5177_: *mut crate::leanh::LeanObject,
    mut v_f_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
    mut v___y_5184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_alt_5177_) {
        0 => {
            let mut v_code_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_5186_ = crate::leanh::lean_ctor_get(v_alt_5177_, 2);
            crate::leanh::lean_inc_ref(v_code_5186_);
            crate::leanh::lean_dec_ref_known(v_alt_5177_, 3);
            crate::leanh::lean_inc(v___y_5184_);
            crate::leanh::lean_inc_ref(v___y_5183_);
            crate::leanh::lean_inc(v___y_5182_);
            crate::leanh::lean_inc_ref(v___y_5181_);
            crate::leanh::lean_inc(v___y_5180_);
            crate::leanh::lean_inc(v___y_5179_);
            v___x_5187_ = crate::leanh::lean_apply_8(
                v_f_5178_,
                v_code_5186_,
                v___y_5179_,
                v___y_5180_,
                v___y_5181_,
                v___y_5182_,
                v___y_5183_,
                v___y_5184_,
                crate::leanh::lean_box(0),
            );
            return v___x_5187_;
        }
        1 => {
            let mut v_code_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_5188_ = crate::leanh::lean_ctor_get(v_alt_5177_, 1);
            crate::leanh::lean_inc_ref(v_code_5188_);
            crate::leanh::lean_dec_ref_known(v_alt_5177_, 2);
            crate::leanh::lean_inc(v___y_5184_);
            crate::leanh::lean_inc_ref(v___y_5183_);
            crate::leanh::lean_inc(v___y_5182_);
            crate::leanh::lean_inc_ref(v___y_5181_);
            crate::leanh::lean_inc(v___y_5180_);
            crate::leanh::lean_inc(v___y_5179_);
            v___x_5189_ = crate::leanh::lean_apply_8(
                v_f_5178_,
                v_code_5188_,
                v___y_5179_,
                v___y_5180_,
                v___y_5181_,
                v___y_5182_,
                v___y_5183_,
                v___y_5184_,
                crate::leanh::lean_box(0),
            );
            return v___x_5189_;
        }
        _ => {
            let mut v_code_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_5190_ = crate::leanh::lean_ctor_get(v_alt_5177_, 0);
            crate::leanh::lean_inc_ref(v_code_5190_);
            crate::leanh::lean_dec_ref_known(v_alt_5177_, 1);
            crate::leanh::lean_inc(v___y_5184_);
            crate::leanh::lean_inc_ref(v___y_5183_);
            crate::leanh::lean_inc(v___y_5182_);
            crate::leanh::lean_inc_ref(v___y_5181_);
            crate::leanh::lean_inc(v___y_5180_);
            crate::leanh::lean_inc(v___y_5179_);
            v___x_5191_ = crate::leanh::lean_apply_8(
                v_f_5178_,
                v_code_5190_,
                v___y_5179_,
                v___y_5180_,
                v___y_5181_,
                v___y_5182_,
                v___y_5183_,
                v___y_5184_,
                crate::leanh::lean_box(0),
            );
            return v___x_5191_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg___boxed(
    mut v_alt_5192_: *mut crate::leanh::LeanObject,
    mut v_f_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
    mut v___y_5195_: *mut crate::leanh::LeanObject,
    mut v___y_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5201_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_5192_, v_f_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
    crate::leanh::lean_dec(v___y_5199_);
    crate::leanh::lean_dec_ref(v___y_5198_);
    crate::leanh::lean_dec(v___y_5197_);
    crate::leanh::lean_dec_ref(v___y_5196_);
    crate::leanh::lean_dec(v___y_5195_);
    crate::leanh::lean_dec(v___y_5194_);
    return v_res_5201_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5202_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5202_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(
    mut v_msg_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v_toFunctor_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v___f_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5244_: u8 = 0;
    let mut v_toFunctor_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___f_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9302__overap_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5272_: u8 = 0;
    let mut v_unused_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_unused_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v_unused_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5280_: u8 = 0;
    let mut v_unused_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5215_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
                v___x_5216_ = l_StateRefT_x27_instMonad___redArg(v___x_5215_);
                v_toApplicative_5217_ = crate::leanh::lean_ctor_get(v___x_5216_, 0);
                v_isSharedCheck_5280_ = (!crate::leanh::lean_is_exclusive(v___x_5216_)) as u8;
                if v_isSharedCheck_5280_ == 0 {
                    v_unused_5281_ = crate::leanh::lean_ctor_get(v___x_5216_, 1);
                    crate::leanh::lean_dec(v_unused_5281_);
                    v___x_5219_ = v___x_5216_;
                    v_isShared_5220_ = v_isSharedCheck_5280_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5217_);
                    crate::leanh::lean_dec(v___x_5216_);
                    v___x_5219_ = crate::leanh::lean_box(0);
                    v_isShared_5220_ = v_isSharedCheck_5280_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5221_ = crate::leanh::lean_ctor_get(v_toApplicative_5217_, 0);
                v_toSeq_5222_ = crate::leanh::lean_ctor_get(v_toApplicative_5217_, 2);
                v_toSeqLeft_5223_ = crate::leanh::lean_ctor_get(v_toApplicative_5217_, 3);
                v_toSeqRight_5224_ = crate::leanh::lean_ctor_get(v_toApplicative_5217_, 4);
                v_isSharedCheck_5278_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5217_)) as u8;
                if v_isSharedCheck_5278_ == 0 {
                    v_unused_5279_ = crate::leanh::lean_ctor_get(v_toApplicative_5217_, 1);
                    crate::leanh::lean_dec(v_unused_5279_);
                    v___x_5226_ = v_toApplicative_5217_;
                    v_isShared_5227_ = v_isSharedCheck_5278_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5224_);
                    crate::leanh::lean_inc(v_toSeqLeft_5223_);
                    crate::leanh::lean_inc(v_toSeq_5222_);
                    crate::leanh::lean_inc(v_toFunctor_5221_);
                    crate::leanh::lean_dec(v_toApplicative_5217_);
                    v___x_5226_ = crate::leanh::lean_box(0);
                    v_isShared_5227_ = v_isSharedCheck_5278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5228_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1;
                v___f_5229_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_5221_);
                v___f_5230_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5230_, 0, v_toFunctor_5221_);
                v___f_5231_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5231_, 0, v_toFunctor_5221_);
                v___x_5232_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5232_, 0, v___f_5230_);
                crate::leanh::lean_ctor_set(v___x_5232_, 1, v___f_5231_);
                v___f_5233_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5233_, 0, v_toSeqRight_5224_);
                v___f_5234_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5234_, 0, v_toSeqLeft_5223_);
                v___f_5235_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5235_, 0, v_toSeq_5222_);
                if v_isShared_5227_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5226_, 4, v___f_5233_);
                    crate::leanh::lean_ctor_set(v___x_5226_, 3, v___f_5234_);
                    crate::leanh::lean_ctor_set(v___x_5226_, 2, v___f_5235_);
                    crate::leanh::lean_ctor_set(v___x_5226_, 1, v___f_5228_);
                    crate::leanh::lean_ctor_set(v___x_5226_, 0, v___x_5232_);
                    v___x_5237_ = v___x_5226_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5277_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 0, v___x_5232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 1, v___f_5228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 2, v___f_5235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 3, v___f_5234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 4, v___f_5233_);
                    v___x_5237_ = v_reuseFailAlloc_5277_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5219_, 1, v___f_5229_);
                    crate::leanh::lean_ctor_set(v___x_5219_, 0, v___x_5237_);
                    v___x_5239_ = v___x_5219_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5276_, 0, v___x_5237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5276_, 1, v___f_5229_);
                    v___x_5239_ = v_reuseFailAlloc_5276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5240_ = l_StateRefT_x27_instMonad___redArg(v___x_5239_);
                v_toApplicative_5241_ = crate::leanh::lean_ctor_get(v___x_5240_, 0);
                v_isSharedCheck_5274_ = (!crate::leanh::lean_is_exclusive(v___x_5240_)) as u8;
                if v_isSharedCheck_5274_ == 0 {
                    v_unused_5275_ = crate::leanh::lean_ctor_get(v___x_5240_, 1);
                    crate::leanh::lean_dec(v_unused_5275_);
                    v___x_5243_ = v___x_5240_;
                    v_isShared_5244_ = v_isSharedCheck_5274_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5241_);
                    crate::leanh::lean_dec(v___x_5240_);
                    v___x_5243_ = crate::leanh::lean_box(0);
                    v_isShared_5244_ = v_isSharedCheck_5274_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5245_ = crate::leanh::lean_ctor_get(v_toApplicative_5241_, 0);
                v_toSeq_5246_ = crate::leanh::lean_ctor_get(v_toApplicative_5241_, 2);
                v_toSeqLeft_5247_ = crate::leanh::lean_ctor_get(v_toApplicative_5241_, 3);
                v_toSeqRight_5248_ = crate::leanh::lean_ctor_get(v_toApplicative_5241_, 4);
                v_isSharedCheck_5272_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5241_)) as u8;
                if v_isSharedCheck_5272_ == 0 {
                    v_unused_5273_ = crate::leanh::lean_ctor_get(v_toApplicative_5241_, 1);
                    crate::leanh::lean_dec(v_unused_5273_);
                    v___x_5250_ = v_toApplicative_5241_;
                    v_isShared_5251_ = v_isSharedCheck_5272_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5248_);
                    crate::leanh::lean_inc(v_toSeqLeft_5247_);
                    crate::leanh::lean_inc(v_toSeq_5246_);
                    crate::leanh::lean_inc(v_toFunctor_5245_);
                    crate::leanh::lean_dec(v_toApplicative_5241_);
                    v___x_5250_ = crate::leanh::lean_box(0);
                    v_isShared_5251_ = v_isSharedCheck_5272_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5252_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3;
                v___f_5253_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_5245_);
                v___f_5254_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5254_, 0, v_toFunctor_5245_);
                v___f_5255_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5255_, 0, v_toFunctor_5245_);
                v___x_5256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5256_, 0, v___f_5254_);
                crate::leanh::lean_ctor_set(v___x_5256_, 1, v___f_5255_);
                v___f_5257_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5257_, 0, v_toSeqRight_5248_);
                v___f_5258_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5258_, 0, v_toSeqLeft_5247_);
                v___f_5259_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5259_, 0, v_toSeq_5246_);
                if v_isShared_5251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5250_, 4, v___f_5257_);
                    crate::leanh::lean_ctor_set(v___x_5250_, 3, v___f_5258_);
                    crate::leanh::lean_ctor_set(v___x_5250_, 2, v___f_5259_);
                    crate::leanh::lean_ctor_set(v___x_5250_, 1, v___f_5252_);
                    crate::leanh::lean_ctor_set(v___x_5250_, 0, v___x_5256_);
                    v___x_5261_ = v___x_5250_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5271_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 0, v___x_5256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 1, v___f_5252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 2, v___f_5259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 3, v___f_5258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 4, v___f_5257_);
                    v___x_5261_ = v_reuseFailAlloc_5271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5243_, 1, v___f_5253_);
                    crate::leanh::lean_ctor_set(v___x_5243_, 0, v___x_5261_);
                    v___x_5263_ = v___x_5243_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 0, v___x_5261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 1, v___f_5253_);
                    v___x_5263_ = v_reuseFailAlloc_5270_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5264_ = l_ReaderT_instMonad___redArg(v___x_5263_);
                v___x_5265_ = l_StateRefT_x27_instMonad___redArg(v___x_5264_);
                v___x_5266_ = crate::leanh::lean_box(0);
                v___x_5267_ = l_instInhabitedOfMonad___redArg(v___x_5265_, v___x_5266_);
                v___x_9302__overap_5268_ = lean_panic_fn_borrowed(v___x_5267_, v_msg_5207_);
                crate::leanh::lean_dec(v___x_5267_);
                crate::leanh::lean_inc(v___y_5213_);
                crate::leanh::lean_inc_ref(v___y_5212_);
                crate::leanh::lean_inc(v___y_5211_);
                crate::leanh::lean_inc_ref(v___y_5210_);
                crate::leanh::lean_inc(v___y_5209_);
                crate::leanh::lean_inc(v___y_5208_);
                v___x_5269_ = crate::leanh::lean_apply_7(
                    v___x_9302__overap_5268_,
                    v___y_5208_,
                    v___y_5209_,
                    v___y_5210_,
                    v___y_5211_,
                    v___y_5212_,
                    v___y_5213_,
                    crate::leanh::lean_box(0),
                );
                return v___x_5269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___boxed(
    mut v_msg_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
    mut v___y_5284_: *mut crate::leanh::LeanObject,
    mut v___y_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
    mut v___y_5287_: *mut crate::leanh::LeanObject,
    mut v___y_5288_: *mut crate::leanh::LeanObject,
    mut v___y_5289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5290_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v_msg_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_);
    crate::leanh::lean_dec(v___y_5288_);
    crate::leanh::lean_dec_ref(v___y_5287_);
    crate::leanh::lean_dec(v___y_5286_);
    crate::leanh::lean_dec_ref(v___y_5285_);
    crate::leanh::lean_dec(v___y_5284_);
    crate::leanh::lean_dec(v___y_5283_);
    return v_res_5290_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5294_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__2;
    v___x_5295_ = crate::leanh::lean_unsigned_to_nat(40);
    v___x_5296_ = crate::leanh::lean_unsigned_to_nat(49);
    v___x_5297_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__1;
    v___x_5298_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__0;
    v___x_5299_ = l_mkPanicMessageWithDecl(
        v___x_5298_,
        v___x_5297_,
        v___x_5296_,
        v___x_5295_,
        v___x_5294_,
    );
    return v___x_5299_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(
    mut v_f_5300_: *mut crate::leanh::LeanObject,
    mut v_e_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ty_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: u8 = 0;
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5314_ = l_Lean_Expr_hasFVar(v_e_5301_);
                if v___x_5314_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_5301_);
                    crate::leanh::lean_dec_ref(v_f_5300_);
                    v___x_5315_ = crate::leanh::lean_box(0);
                    v___x_5316_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5316_, 0, v___x_5315_);
                    return v___x_5316_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_5301_) {
                        1 => {
                            v_fvarId_5317_ = crate::leanh::lean_ctor_get(v_e_5301_, 0);
                            crate::leanh::lean_inc(v_fvarId_5317_);
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 1);
                            crate::leanh::lean_inc(v___y_5307_);
                            crate::leanh::lean_inc_ref(v___y_5306_);
                            crate::leanh::lean_inc(v___y_5305_);
                            crate::leanh::lean_inc_ref(v___y_5304_);
                            crate::leanh::lean_inc(v___y_5303_);
                            crate::leanh::lean_inc(v___y_5302_);
                            v___x_5318_ = crate::leanh::lean_apply_8(
                                v_f_5300_,
                                v_fvarId_5317_,
                                v___y_5302_,
                                v___y_5303_,
                                v___y_5304_,
                                v___y_5305_,
                                v___y_5306_,
                                v___y_5307_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_5318_;
                        }
                        2 => {
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 1);
                            crate::leanh::lean_dec_ref(v_f_5300_);
                            v___x_5319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
                            v___x_5320_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_5319_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
                            return v___x_5320_;
                        }
                        5 => {
                            v_fn_5321_ = crate::leanh::lean_ctor_get(v_e_5301_, 0);
                            crate::leanh::lean_inc_ref(v_fn_5321_);
                            v_arg_5322_ = crate::leanh::lean_ctor_get(v_e_5301_, 1);
                            crate::leanh::lean_inc_ref(v_arg_5322_);
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 2);
                            crate::leanh::lean_inc_ref(v_f_5300_);
                            v___x_5323_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5300_, v_fn_5321_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
                            if crate::leanh::lean_obj_tag(v___x_5323_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5323_, 1);
                                v_e_5301_ = v_arg_5322_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_arg_5322_);
                                crate::leanh::lean_dec_ref(v_f_5300_);
                                return v___x_5323_;
                            }
                        }
                        6 => {
                            v_binderType_5325_ = crate::leanh::lean_ctor_get(v_e_5301_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_5325_);
                            v_body_5326_ = crate::leanh::lean_ctor_get(v_e_5301_, 2);
                            crate::leanh::lean_inc_ref(v_body_5326_);
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 3);
                            v_ty_5310_ = v_binderType_5325_;
                            v_body_5311_ = v_body_5326_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderType_5327_ = crate::leanh::lean_ctor_get(v_e_5301_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_5327_);
                            v_body_5328_ = crate::leanh::lean_ctor_get(v_e_5301_, 2);
                            crate::leanh::lean_inc_ref(v_body_5328_);
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 3);
                            v_ty_5310_ = v_binderType_5327_;
                            v_body_5311_ = v_body_5328_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 4);
                            crate::leanh::lean_dec_ref(v_f_5300_);
                            v___x_5329_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
                            v___x_5330_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_5329_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
                            return v___x_5330_;
                        }
                        11 => {
                            crate::leanh::lean_dec_ref_known(v_e_5301_, 3);
                            crate::leanh::lean_dec_ref(v_f_5300_);
                            v___x_5331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
                            v___x_5332_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1(v___x_5331_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
                            return v___x_5332_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_5301_);
                            crate::leanh::lean_dec_ref(v_f_5300_);
                            v___x_5333_ = crate::leanh::lean_box(0);
                            v___x_5334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5334_, 0, v___x_5333_);
                            return v___x_5334_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_5300_);
                v___x_5312_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5300_, v_ty_5310_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
                if crate::leanh::lean_obj_tag(v___x_5312_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5312_, 1);
                    v_e_5301_ = v_body_5311_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_5311_);
                    crate::leanh::lean_dec_ref(v_f_5300_);
                    return v___x_5312_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___boxed(
    mut v_f_5335_: *mut crate::leanh::LeanObject,
    mut v_e_5336_: *mut crate::leanh::LeanObject,
    mut v___y_5337_: *mut crate::leanh::LeanObject,
    mut v___y_5338_: *mut crate::leanh::LeanObject,
    mut v___y_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5344_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5335_, v_e_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
    crate::leanh::lean_dec(v___y_5342_);
    crate::leanh::lean_dec_ref(v___y_5341_);
    crate::leanh::lean_dec(v___y_5340_);
    crate::leanh::lean_dec_ref(v___y_5339_);
    crate::leanh::lean_dec(v___y_5338_);
    crate::leanh::lean_dec(v___y_5337_);
    return v_res_5344_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(
    mut v_f_5345_: *mut crate::leanh::LeanObject,
    mut v_param_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_5354_ = crate::leanh::lean_ctor_get(v_param_5346_, 2);
    crate::leanh::lean_inc_ref(v_type_5354_);
    crate::leanh::lean_dec_ref(v_param_5346_);
    v___x_5355_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5345_, v_type_5354_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
    return v___x_5355_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg___boxed(
    mut v_f_5356_: *mut crate::leanh::LeanObject,
    mut v_param_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5365_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_5356_, v_param_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
    crate::leanh::lean_dec(v___y_5363_);
    crate::leanh::lean_dec_ref(v___y_5362_);
    crate::leanh::lean_dec(v___y_5361_);
    crate::leanh::lean_dec_ref(v___y_5360_);
    crate::leanh::lean_dec(v___y_5359_);
    crate::leanh::lean_dec(v___y_5358_);
    return v_res_5365_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(
    mut v_pu_5366_: u8,
    mut v_f_5367_: *mut crate::leanh::LeanObject,
    mut v_as_5368_: *mut crate::leanh::LeanObject,
    mut v_i_5369_: usize,
    mut v_stop_5370_: usize,
    mut v_b_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5379_: u8 = 0;
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: usize = 0;
    let mut v___x_5384_: usize = 0;
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5379_ = lean_usize_dec_eq(v_i_5369_, v_stop_5370_);
                if v___x_5379_ == 0 {
                    v___x_5380_ = lean_array_uget_borrowed(v_as_5368_, v_i_5369_);
                    crate::leanh::lean_inc(v___x_5380_);
                    crate::leanh::lean_inc_ref(v_f_5367_);
                    v___x_5381_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_5367_, v___x_5380_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
                    if crate::leanh::lean_obj_tag(v___x_5381_) == 0 {
                        v_a_5382_ = crate::leanh::lean_ctor_get(v___x_5381_, 0);
                        crate::leanh::lean_inc(v_a_5382_);
                        crate::leanh::lean_dec_ref_known(v___x_5381_, 1);
                        v___x_5383_ = 1usize;
                        v___x_5384_ = lean_usize_add(v_i_5369_, v___x_5383_);
                        v_i_5369_ = v___x_5384_;
                        v_b_5371_ = v_a_5382_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_5367_);
                        return v___x_5381_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5367_);
                    v___x_5386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5386_, 0, v_b_5371_);
                    return v___x_5386_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5___boxed(
    mut v_pu_5387_: *mut crate::leanh::LeanObject,
    mut v_f_5388_: *mut crate::leanh::LeanObject,
    mut v_as_5389_: *mut crate::leanh::LeanObject,
    mut v_i_5390_: *mut crate::leanh::LeanObject,
    mut v_stop_5391_: *mut crate::leanh::LeanObject,
    mut v_b_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
    mut v___y_5394_: *mut crate::leanh::LeanObject,
    mut v___y_5395_: *mut crate::leanh::LeanObject,
    mut v___y_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
    mut v___y_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5400_: u8 = 0;
    let mut v_i_boxed_5401_: usize = 0;
    let mut v_stop_boxed_5402_: usize = 0;
    let mut v_res_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5400_ = (crate::leanh::lean_unbox(v_pu_5387_) as u8);
    v_i_boxed_5401_ = crate::leanh::lean_unbox_usize(v_i_5390_);
    crate::leanh::lean_dec(v_i_5390_);
    v_stop_boxed_5402_ = crate::leanh::lean_unbox_usize(v_stop_5391_);
    crate::leanh::lean_dec(v_stop_5391_);
    v_res_5403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_boxed_5400_, v_f_5388_, v_as_5389_, v_i_boxed_5401_, v_stop_boxed_5402_, v_b_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_);
    crate::leanh::lean_dec(v___y_5398_);
    crate::leanh::lean_dec_ref(v___y_5397_);
    crate::leanh::lean_dec(v___y_5396_);
    crate::leanh::lean_dec_ref(v___y_5395_);
    crate::leanh::lean_dec(v___y_5394_);
    crate::leanh::lean_dec(v___y_5393_);
    crate::leanh::lean_dec_ref(v_as_5389_);
    return v_res_5403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(
    mut v_f_5404_: *mut crate::leanh::LeanObject,
    mut v_arg_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
    mut v___y_5411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_arg_5405_) {
        0 => {
            let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_f_5404_);
            v___x_5413_ = crate::leanh::lean_box(0);
            v___x_5414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_5414_, 0, v___x_5413_);
            return v___x_5414_;
        }
        1 => {
            let mut v_fvarId_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_5415_ = crate::leanh::lean_ctor_get(v_arg_5405_, 0);
            crate::leanh::lean_inc(v_fvarId_5415_);
            crate::leanh::lean_dec_ref_known(v_arg_5405_, 1);
            crate::leanh::lean_inc(v___y_5411_);
            crate::leanh::lean_inc_ref(v___y_5410_);
            crate::leanh::lean_inc(v___y_5409_);
            crate::leanh::lean_inc_ref(v___y_5408_);
            crate::leanh::lean_inc(v___y_5407_);
            crate::leanh::lean_inc(v___y_5406_);
            v___x_5416_ = crate::leanh::lean_apply_8(
                v_f_5404_,
                v_fvarId_5415_,
                v___y_5406_,
                v___y_5407_,
                v___y_5408_,
                v___y_5409_,
                v___y_5410_,
                v___y_5411_,
                crate::leanh::lean_box(0),
            );
            return v___x_5416_;
        }
        _ => {
            let mut v_expr_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_expr_5417_ = crate::leanh::lean_ctor_get(v_arg_5405_, 0);
            crate::leanh::lean_inc_ref(v_expr_5417_);
            crate::leanh::lean_dec_ref_known(v_arg_5405_, 1);
            v___x_5418_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5404_, v_expr_5417_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_);
            return v___x_5418_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg___boxed(
    mut v_f_5419_: *mut crate::leanh::LeanObject,
    mut v_arg_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5428_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_5419_, v_arg_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
    crate::leanh::lean_dec(v___y_5426_);
    crate::leanh::lean_dec_ref(v___y_5425_);
    crate::leanh::lean_dec(v___y_5424_);
    crate::leanh::lean_dec_ref(v___y_5423_);
    crate::leanh::lean_dec(v___y_5422_);
    crate::leanh::lean_dec(v___y_5421_);
    return v_res_5428_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(
    mut v_pu_5429_: u8,
    mut v_f_5430_: *mut crate::leanh::LeanObject,
    mut v_as_5431_: *mut crate::leanh::LeanObject,
    mut v_i_5432_: usize,
    mut v_stop_5433_: usize,
    mut v_b_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
    mut v___y_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5442_: u8 = 0;
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: usize = 0;
    let mut v___x_5447_: usize = 0;
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5442_ = lean_usize_dec_eq(v_i_5432_, v_stop_5433_);
                if v___x_5442_ == 0 {
                    v___x_5443_ = lean_array_uget_borrowed(v_as_5431_, v_i_5432_);
                    crate::leanh::lean_inc(v___x_5443_);
                    crate::leanh::lean_inc_ref(v_f_5430_);
                    v___x_5444_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_5430_, v___x_5443_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
                    if crate::leanh::lean_obj_tag(v___x_5444_) == 0 {
                        v_a_5445_ = crate::leanh::lean_ctor_get(v___x_5444_, 0);
                        crate::leanh::lean_inc(v_a_5445_);
                        crate::leanh::lean_dec_ref_known(v___x_5444_, 1);
                        v___x_5446_ = 1usize;
                        v___x_5447_ = lean_usize_add(v_i_5432_, v___x_5446_);
                        v_i_5432_ = v___x_5447_;
                        v_b_5434_ = v_a_5445_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_5430_);
                        return v___x_5444_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5430_);
                    v___x_5449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5449_, 0, v_b_5434_);
                    return v___x_5449_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6___boxed(
    mut v_pu_5450_: *mut crate::leanh::LeanObject,
    mut v_f_5451_: *mut crate::leanh::LeanObject,
    mut v_as_5452_: *mut crate::leanh::LeanObject,
    mut v_i_5453_: *mut crate::leanh::LeanObject,
    mut v_stop_5454_: *mut crate::leanh::LeanObject,
    mut v_b_5455_: *mut crate::leanh::LeanObject,
    mut v___y_5456_: *mut crate::leanh::LeanObject,
    mut v___y_5457_: *mut crate::leanh::LeanObject,
    mut v___y_5458_: *mut crate::leanh::LeanObject,
    mut v___y_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5463_: u8 = 0;
    let mut v_i_boxed_5464_: usize = 0;
    let mut v_stop_boxed_5465_: usize = 0;
    let mut v_res_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5463_ = (crate::leanh::lean_unbox(v_pu_5450_) as u8);
    v_i_boxed_5464_ = crate::leanh::lean_unbox_usize(v_i_5453_);
    crate::leanh::lean_dec(v_i_5453_);
    v_stop_boxed_5465_ = crate::leanh::lean_unbox_usize(v_stop_5454_);
    crate::leanh::lean_dec(v_stop_5454_);
    v_res_5466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_boxed_5463_, v_f_5451_, v_as_5452_, v_i_boxed_5464_, v_stop_boxed_5465_, v_b_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_);
    crate::leanh::lean_dec(v___y_5461_);
    crate::leanh::lean_dec_ref(v___y_5460_);
    crate::leanh::lean_dec(v___y_5459_);
    crate::leanh::lean_dec_ref(v___y_5458_);
    crate::leanh::lean_dec(v___y_5457_);
    crate::leanh::lean_dec(v___y_5456_);
    crate::leanh::lean_dec_ref(v_as_5452_);
    return v_res_5466_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(
    mut v_pu_5467_: u8,
    mut v_f_5468_: *mut crate::leanh::LeanObject,
    mut v_e_5469_: *mut crate::leanh::LeanObject,
    mut v___y_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: *mut crate::leanh::LeanObject,
    mut v___y_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: u8 = 0;
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: usize = 0;
    let mut v___x_5487_: usize = 0;
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: usize = 0;
    let mut v___x_5490_: usize = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: u8 = 0;
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: usize = 0;
    let mut v___x_5503_: usize = 0;
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: usize = 0;
    let mut v___x_5506_: usize = 0;
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: u8 = 0;
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: usize = 0;
    let mut v___x_5526_: usize = 0;
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: usize = 0;
    let mut v___x_5529_: usize = 0;
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_unused_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: u8 = 0;
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: u8 = 0;
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: usize = 0;
    let mut v___x_5542_: usize = 0;
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: usize = 0;
    let mut v___x_5545_: usize = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: u8 = 0;
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: usize = 0;
    let mut v___x_5575_: usize = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: usize = 0;
    let mut v___x_5578_: usize = 0;
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_unused_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_5469_) {
                2 => {
                    v_struct_5492_ = crate::leanh::lean_ctor_get(v_e_5469_, 2);
                    crate::leanh::lean_inc(v_struct_5492_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 3);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5493_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_struct_5492_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5493_;
                }
                3 => {
                    v_args_5494_ = crate::leanh::lean_ctor_get(v_e_5469_, 2);
                    crate::leanh::lean_inc_ref(v_args_5494_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 3);
                    v___x_5495_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5496_ = lean_array_get_size(v_args_5494_);
                    v___x_5497_ = crate::leanh::lean_box(0);
                    v___x_5498_ = lean_nat_dec_lt(v___x_5495_, v___x_5496_);
                    if v___x_5498_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_5494_);
                        crate::leanh::lean_dec_ref(v_f_5468_);
                        v___x_5499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5499_, 0, v___x_5497_);
                        return v___x_5499_;
                    } else {
                        v___x_5500_ = lean_nat_dec_le(v___x_5496_, v___x_5496_);
                        if v___x_5500_ == 0 {
                            if v___x_5498_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_5494_);
                                crate::leanh::lean_dec_ref(v_f_5468_);
                                v___x_5501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5501_, 0, v___x_5497_);
                                return v___x_5501_;
                            } else {
                                v___x_5502_ = 0usize;
                                v___x_5503_ = lean_usize_of_nat(v___x_5496_);
                                v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5494_, v___x_5502_, v___x_5503_, v___x_5497_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                                crate::leanh::lean_dec_ref(v_args_5494_);
                                return v___x_5504_;
                            }
                        } else {
                            v___x_5505_ = 0usize;
                            v___x_5506_ = lean_usize_of_nat(v___x_5496_);
                            v___x_5507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5494_, v___x_5505_, v___x_5506_, v___x_5497_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                            crate::leanh::lean_dec_ref(v_args_5494_);
                            return v___x_5507_;
                        }
                    }
                }
                4 => {
                    v_fvarId_5508_ = crate::leanh::lean_ctor_get(v_e_5469_, 0);
                    crate::leanh::lean_inc(v_fvarId_5508_);
                    v_args_5509_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc_ref(v_args_5509_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    crate::leanh::lean_inc_ref(v_f_5468_);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5510_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_fvarId_5508_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5510_) == 0 {
                        v_isSharedCheck_5531_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5510_)) as u8;
                        if v_isSharedCheck_5531_ == 0 {
                            v_unused_5532_ = crate::leanh::lean_ctor_get(v___x_5510_, 0);
                            crate::leanh::lean_dec(v_unused_5532_);
                            v___x_5512_ = v___x_5510_;
                            v_isShared_5513_ = v_isSharedCheck_5531_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5510_);
                            v___x_5512_ = crate::leanh::lean_box(0);
                            v_isShared_5513_ = v_isSharedCheck_5531_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_5509_);
                        crate::leanh::lean_dec_ref(v_f_5468_);
                        return v___x_5510_;
                    }
                }
                5 => {
                    v_args_5533_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc_ref(v_args_5533_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    v___x_5534_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5535_ = lean_array_get_size(v_args_5533_);
                    v___x_5536_ = crate::leanh::lean_box(0);
                    v___x_5537_ = lean_nat_dec_lt(v___x_5534_, v___x_5535_);
                    if v___x_5537_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_5533_);
                        crate::leanh::lean_dec_ref(v_f_5468_);
                        v___x_5538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5538_, 0, v___x_5536_);
                        return v___x_5538_;
                    } else {
                        v___x_5539_ = lean_nat_dec_le(v___x_5535_, v___x_5535_);
                        if v___x_5539_ == 0 {
                            if v___x_5537_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_5533_);
                                crate::leanh::lean_dec_ref(v_f_5468_);
                                v___x_5540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5540_, 0, v___x_5536_);
                                return v___x_5540_;
                            } else {
                                v___x_5541_ = 0usize;
                                v___x_5542_ = lean_usize_of_nat(v___x_5535_);
                                v___x_5543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5533_, v___x_5541_, v___x_5542_, v___x_5536_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                                crate::leanh::lean_dec_ref(v_args_5533_);
                                return v___x_5543_;
                            }
                        } else {
                            v___x_5544_ = 0usize;
                            v___x_5545_ = lean_usize_of_nat(v___x_5535_);
                            v___x_5546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5533_, v___x_5544_, v___x_5545_, v___x_5536_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                            crate::leanh::lean_dec_ref(v_args_5533_);
                            return v___x_5546_;
                        }
                    }
                }
                6 => {
                    v_var_5547_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc(v_var_5547_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5548_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_var_5547_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5548_;
                }
                7 => {
                    v_var_5549_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc(v_var_5549_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5550_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_var_5549_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5550_;
                }
                8 => {
                    v_var_5551_ = crate::leanh::lean_ctor_get(v_e_5469_, 2);
                    crate::leanh::lean_inc(v_var_5551_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 3);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5552_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_var_5551_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5552_;
                }
                9 => {
                    v_args_5553_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc_ref(v_args_5553_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    v_args_5478_ = v_args_5553_;
                    state = 1;
                    continue;
                }
                10 => {
                    v_args_5554_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc_ref(v_args_5554_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    v_args_5478_ = v_args_5554_;
                    state = 1;
                    continue;
                }
                11 => {
                    v_var_5555_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc(v_var_5555_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5556_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_var_5555_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5556_;
                }
                12 => {
                    v_var_5557_ = crate::leanh::lean_ctor_get(v_e_5469_, 0);
                    crate::leanh::lean_inc(v_var_5557_);
                    v_args_5558_ = crate::leanh::lean_ctor_get(v_e_5469_, 2);
                    crate::leanh::lean_inc_ref(v_args_5558_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 3);
                    crate::leanh::lean_inc_ref(v_f_5468_);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5559_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_var_5557_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5559_) == 0 {
                        v_isSharedCheck_5580_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5559_)) as u8;
                        if v_isSharedCheck_5580_ == 0 {
                            v_unused_5581_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
                            crate::leanh::lean_dec(v_unused_5581_);
                            v___x_5561_ = v___x_5559_;
                            v_isShared_5562_ = v_isSharedCheck_5580_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5559_);
                            v___x_5561_ = crate::leanh::lean_box(0);
                            v_isShared_5562_ = v_isSharedCheck_5580_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_5558_);
                        crate::leanh::lean_dec_ref(v_f_5468_);
                        return v___x_5559_;
                    }
                }
                13 => {
                    v_fvarId_5582_ = crate::leanh::lean_ctor_get(v_e_5469_, 1);
                    crate::leanh::lean_inc(v_fvarId_5582_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 2);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5583_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_fvarId_5582_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5583_;
                }
                14 => {
                    v_fvarId_5584_ = crate::leanh::lean_ctor_get(v_e_5469_, 0);
                    crate::leanh::lean_inc(v_fvarId_5584_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 1);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5585_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_fvarId_5584_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5585_;
                }
                15 => {
                    v_fvarId_5586_ = crate::leanh::lean_ctor_get(v_e_5469_, 0);
                    crate::leanh::lean_inc(v_fvarId_5586_);
                    crate::leanh::lean_dec_ref_known(v_e_5469_, 1);
                    crate::leanh::lean_inc(v___y_5475_);
                    crate::leanh::lean_inc_ref(v___y_5474_);
                    crate::leanh::lean_inc(v___y_5473_);
                    crate::leanh::lean_inc_ref(v___y_5472_);
                    crate::leanh::lean_inc(v___y_5471_);
                    crate::leanh::lean_inc(v___y_5470_);
                    v___x_5587_ = crate::leanh::lean_apply_8(
                        v_f_5468_,
                        v_fvarId_5586_,
                        v___y_5470_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                        v___y_5475_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5587_;
                }
                _ => {
                    crate::leanh::lean_dec(v_e_5469_);
                    crate::leanh::lean_dec_ref(v_f_5468_);
                    v___x_5588_ = crate::leanh::lean_box(0);
                    v___x_5589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5589_, 0, v___x_5588_);
                    return v___x_5589_;
                }
            },
            1 => {
                v___x_5479_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5480_ = lean_array_get_size(v_args_5478_);
                v___x_5481_ = crate::leanh::lean_box(0);
                v___x_5482_ = lean_nat_dec_lt(v___x_5479_, v___x_5480_);
                if v___x_5482_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_5478_);
                    crate::leanh::lean_dec_ref(v_f_5468_);
                    v___x_5483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5483_, 0, v___x_5481_);
                    return v___x_5483_;
                } else {
                    v___x_5484_ = lean_nat_dec_le(v___x_5480_, v___x_5480_);
                    if v___x_5484_ == 0 {
                        if v___x_5482_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_5478_);
                            crate::leanh::lean_dec_ref(v_f_5468_);
                            v___x_5485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5485_, 0, v___x_5481_);
                            return v___x_5485_;
                        } else {
                            v___x_5486_ = 0usize;
                            v___x_5487_ = lean_usize_of_nat(v___x_5480_);
                            v___x_5488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5478_, v___x_5486_, v___x_5487_, v___x_5481_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                            crate::leanh::lean_dec_ref(v_args_5478_);
                            return v___x_5488_;
                        }
                    } else {
                        v___x_5489_ = 0usize;
                        v___x_5490_ = lean_usize_of_nat(v___x_5480_);
                        v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5478_, v___x_5489_, v___x_5490_, v___x_5481_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                        crate::leanh::lean_dec_ref(v_args_5478_);
                        return v___x_5491_;
                    }
                }
            }
            2 => {
                v___x_5514_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5515_ = lean_array_get_size(v_args_5509_);
                v___x_5516_ = crate::leanh::lean_box(0);
                v___x_5517_ = lean_nat_dec_lt(v___x_5514_, v___x_5515_);
                if v___x_5517_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_5509_);
                    crate::leanh::lean_dec_ref(v_f_5468_);
                    if v_isShared_5513_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5512_, 0, v___x_5516_);
                        v___x_5519_ = v___x_5512_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5516_);
                        v___x_5519_ = v_reuseFailAlloc_5520_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5521_ = lean_nat_dec_le(v___x_5515_, v___x_5515_);
                    if v___x_5521_ == 0 {
                        if v___x_5517_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_5509_);
                            crate::leanh::lean_dec_ref(v_f_5468_);
                            if v_isShared_5513_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5512_, 0, v___x_5516_);
                                v___x_5523_ = v___x_5512_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_5524_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5516_);
                                v___x_5523_ = v_reuseFailAlloc_5524_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5512_);
                            v___x_5525_ = 0usize;
                            v___x_5526_ = lean_usize_of_nat(v___x_5515_);
                            v___x_5527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5509_, v___x_5525_, v___x_5526_, v___x_5516_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                            crate::leanh::lean_dec_ref(v_args_5509_);
                            return v___x_5527_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5512_);
                        v___x_5528_ = 0usize;
                        v___x_5529_ = lean_usize_of_nat(v___x_5515_);
                        v___x_5530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5509_, v___x_5528_, v___x_5529_, v___x_5516_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                        crate::leanh::lean_dec_ref(v_args_5509_);
                        return v___x_5530_;
                    }
                }
            }
            3 => {
                return v___x_5519_;
            }
            4 => {
                return v___x_5523_;
            }
            5 => {
                v___x_5563_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5564_ = lean_array_get_size(v_args_5558_);
                v___x_5565_ = crate::leanh::lean_box(0);
                v___x_5566_ = lean_nat_dec_lt(v___x_5563_, v___x_5564_);
                if v___x_5566_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_5558_);
                    crate::leanh::lean_dec_ref(v_f_5468_);
                    if v_isShared_5562_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5561_, 0, v___x_5565_);
                        v___x_5568_ = v___x_5561_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5565_);
                        v___x_5568_ = v_reuseFailAlloc_5569_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_5570_ = lean_nat_dec_le(v___x_5564_, v___x_5564_);
                    if v___x_5570_ == 0 {
                        if v___x_5566_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_5558_);
                            crate::leanh::lean_dec_ref(v_f_5468_);
                            if v_isShared_5562_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5561_, 0, v___x_5565_);
                                v___x_5572_ = v___x_5561_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_5573_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5565_);
                                v___x_5572_ = v_reuseFailAlloc_5573_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5561_);
                            v___x_5574_ = 0usize;
                            v___x_5575_ = lean_usize_of_nat(v___x_5564_);
                            v___x_5576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5558_, v___x_5574_, v___x_5575_, v___x_5565_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                            crate::leanh::lean_dec_ref(v_args_5558_);
                            return v___x_5576_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5561_);
                        v___x_5577_ = 0usize;
                        v___x_5578_ = lean_usize_of_nat(v___x_5564_);
                        v___x_5579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5467_, v_f_5468_, v_args_5558_, v___x_5577_, v___x_5578_, v___x_5565_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
                        crate::leanh::lean_dec_ref(v_args_5558_);
                        return v___x_5579_;
                    }
                }
            }
            6 => {
                return v___x_5568_;
            }
            7 => {
                return v___x_5572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6___boxed(
    mut v_pu_5590_: *mut crate::leanh::LeanObject,
    mut v_f_5591_: *mut crate::leanh::LeanObject,
    mut v_e_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5600_: u8 = 0;
    let mut v_res_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5600_ = (crate::leanh::lean_unbox(v_pu_5590_) as u8);
    v_res_5601_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_boxed_5600_, v_f_5591_, v_e_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    crate::leanh::lean_dec(v___y_5598_);
    crate::leanh::lean_dec_ref(v___y_5597_);
    crate::leanh::lean_dec(v___y_5596_);
    crate::leanh::lean_dec_ref(v___y_5595_);
    crate::leanh::lean_dec(v___y_5594_);
    crate::leanh::lean_dec(v___y_5593_);
    return v_res_5601_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(
    mut v_pu_5602_: u8,
    mut v_f_5603_: *mut crate::leanh::LeanObject,
    mut v_decl_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_5612_ = crate::leanh::lean_ctor_get(v_decl_5604_, 2);
    crate::leanh::lean_inc_ref(v_type_5612_);
    v_value_5613_ = crate::leanh::lean_ctor_get(v_decl_5604_, 3);
    crate::leanh::lean_inc(v_value_5613_);
    crate::leanh::lean_dec_ref(v_decl_5604_);
    crate::leanh::lean_inc_ref(v_f_5603_);
    v___x_5614_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5603_, v_type_5612_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
    if crate::leanh::lean_obj_tag(v___x_5614_) == 0 {
        let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_5614_, 1);
        v___x_5615_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4_spec__6(v_pu_5602_, v_f_5603_, v_value_5613_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
        return v___x_5615_;
    } else {
        crate::leanh::lean_dec(v_value_5613_);
        crate::leanh::lean_dec_ref(v_f_5603_);
        return v___x_5614_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4___boxed(
    mut v_pu_5616_: *mut crate::leanh::LeanObject,
    mut v_f_5617_: *mut crate::leanh::LeanObject,
    mut v_decl_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5626_: u8 = 0;
    let mut v_res_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5626_ = (crate::leanh::lean_unbox(v_pu_5616_) as u8);
    v_res_5627_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_boxed_5626_, v_f_5617_, v_decl_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_);
    crate::leanh::lean_dec(v___y_5624_);
    crate::leanh::lean_dec_ref(v___y_5623_);
    crate::leanh::lean_dec(v___y_5622_);
    crate::leanh::lean_dec_ref(v___y_5621_);
    crate::leanh::lean_dec(v___y_5620_);
    crate::leanh::lean_dec(v___y_5619_);
    return v_res_5627_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed(
    mut v_pu_5628_: *mut crate::leanh::LeanObject,
    mut v_f_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
    mut v___y_5634_: *mut crate::leanh::LeanObject,
    mut v___y_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5638_: u8 = 0;
    let mut v_res_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5638_ = (crate::leanh::lean_unbox(v_pu_5628_) as u8);
    v_res_5639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(v_pu_boxed_5638_, v_f_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
    crate::leanh::lean_dec(v___y_5636_);
    crate::leanh::lean_dec_ref(v___y_5635_);
    crate::leanh::lean_dec(v___y_5634_);
    crate::leanh::lean_dec_ref(v___y_5633_);
    crate::leanh::lean_dec(v___y_5632_);
    crate::leanh::lean_dec(v___y_5631_);
    return v_res_5639_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(
    mut v_pu_5640_: u8,
    mut v_f_5641_: *mut crate::leanh::LeanObject,
    mut v_as_5642_: *mut crate::leanh::LeanObject,
    mut v_i_5643_: usize,
    mut v_stop_5644_: usize,
    mut v_b_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5653_: u8 = 0;
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: usize = 0;
    let mut v___x_5660_: usize = 0;
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5653_ = lean_usize_dec_eq(v_i_5643_, v_stop_5644_);
                if v___x_5653_ == 0 {
                    v___x_5654_ = crate::leanh::lean_box((v_pu_5640_) as usize);
                    crate::leanh::lean_inc_ref(v_f_5641_);
                    v___f_5655_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    crate::leanh::lean_closure_set(v___f_5655_, 0, v___x_5654_);
                    crate::leanh::lean_closure_set(v___f_5655_, 1, v_f_5641_);
                    v___x_5656_ = lean_array_uget_borrowed(v_as_5642_, v_i_5643_);
                    crate::leanh::lean_inc(v___x_5656_);
                    v___x_5657_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v___x_5656_, v___f_5655_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_);
                    if crate::leanh::lean_obj_tag(v___x_5657_) == 0 {
                        v_a_5658_ = crate::leanh::lean_ctor_get(v___x_5657_, 0);
                        crate::leanh::lean_inc(v_a_5658_);
                        crate::leanh::lean_dec_ref_known(v___x_5657_, 1);
                        v___x_5659_ = 1usize;
                        v___x_5660_ = lean_usize_add(v_i_5643_, v___x_5659_);
                        v_i_5643_ = v___x_5660_;
                        v_b_5645_ = v_a_5658_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_5641_);
                        return v___x_5657_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5641_);
                    v___x_5662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5662_, 0, v_b_5645_);
                    return v___x_5662_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(
    mut v_pu_5663_: u8,
    mut v_f_5664_: *mut crate::leanh::LeanObject,
    mut v_c_5665_: *mut crate::leanh::LeanObject,
    mut v___y_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: u8 = 0;
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: usize = 0;
    let mut v___x_5695_: usize = 0;
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: usize = 0;
    let mut v___x_5698_: usize = 0;
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5700_: u8 = 0;
    let mut v_unused_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5710_: u8 = 0;
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: u8 = 0;
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: usize = 0;
    let mut v___x_5723_: usize = 0;
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: usize = 0;
    let mut v___x_5726_: usize = 0;
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5728_: u8 = 0;
    let mut v_unused_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: u8 = 0;
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: u8 = 0;
    let mut v___x_5793_: usize = 0;
    let mut v___x_5794_: usize = 0;
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: usize = 0;
    let mut v___x_5797_: usize = 0;
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_5665_) {
                0 => {
                    v_decl_5673_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5673_);
                    v_k_5674_ = crate::leanh::lean_ctor_get(v_c_5665_, 1);
                    crate::leanh::lean_inc_ref(v_k_5674_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 2);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    v___x_5675_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__4(v_pu_5663_, v_f_5664_, v_decl_5673_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                    if crate::leanh::lean_obj_tag(v___x_5675_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5675_, 1);
                        v_c_5665_ = v_k_5674_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5674_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5675_;
                    }
                }
                3 => {
                    v_fvarId_5677_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5677_);
                    v_args_5678_ = crate::leanh::lean_ctor_get(v_c_5665_, 1);
                    crate::leanh::lean_inc_ref(v_args_5678_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 2);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5679_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5677_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5679_) == 0 {
                        v_isSharedCheck_5700_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5679_)) as u8;
                        if v_isSharedCheck_5700_ == 0 {
                            v_unused_5701_ = crate::leanh::lean_ctor_get(v___x_5679_, 0);
                            crate::leanh::lean_dec(v_unused_5701_);
                            v___x_5681_ = v___x_5679_;
                            v_isShared_5682_ = v_isSharedCheck_5700_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5679_);
                            v___x_5681_ = crate::leanh::lean_box(0);
                            v_isShared_5682_ = v_isSharedCheck_5700_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_5678_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5679_;
                    }
                }
                4 => {
                    v_cases_5702_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc_ref(v_cases_5702_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 1);
                    v_resultType_5703_ = crate::leanh::lean_ctor_get(v_cases_5702_, 1);
                    crate::leanh::lean_inc_ref(v_resultType_5703_);
                    v_discr_5704_ = crate::leanh::lean_ctor_get(v_cases_5702_, 2);
                    crate::leanh::lean_inc(v_discr_5704_);
                    v_alts_5705_ = crate::leanh::lean_ctor_get(v_cases_5702_, 3);
                    crate::leanh::lean_inc_ref(v_alts_5705_);
                    crate::leanh::lean_dec_ref(v_cases_5702_);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    v___x_5706_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5664_, v_resultType_5703_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                    if crate::leanh::lean_obj_tag(v___x_5706_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5706_, 1);
                        crate::leanh::lean_inc_ref(v_f_5664_);
                        crate::leanh::lean_inc(v___y_5671_);
                        crate::leanh::lean_inc_ref(v___y_5670_);
                        crate::leanh::lean_inc(v___y_5669_);
                        crate::leanh::lean_inc_ref(v___y_5668_);
                        crate::leanh::lean_inc(v___y_5667_);
                        crate::leanh::lean_inc(v___y_5666_);
                        v___x_5707_ = crate::leanh::lean_apply_8(
                            v_f_5664_,
                            v_discr_5704_,
                            v___y_5666_,
                            v___y_5667_,
                            v___y_5668_,
                            v___y_5669_,
                            v___y_5670_,
                            v___y_5671_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5707_) == 0 {
                            v_isSharedCheck_5728_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5707_)) as u8;
                            if v_isSharedCheck_5728_ == 0 {
                                v_unused_5729_ = crate::leanh::lean_ctor_get(v___x_5707_, 0);
                                crate::leanh::lean_dec(v_unused_5729_);
                                v___x_5709_ = v___x_5707_;
                                v_isShared_5710_ = v_isSharedCheck_5728_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5707_);
                                v___x_5709_ = crate::leanh::lean_box(0);
                                v_isShared_5710_ = v_isSharedCheck_5728_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_alts_5705_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            return v___x_5707_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_alts_5705_);
                        crate::leanh::lean_dec(v_discr_5704_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5706_;
                    }
                }
                5 => {
                    v_fvarId_5730_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5730_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 1);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5731_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5730_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5731_;
                }
                6 => {
                    v_type_5732_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc_ref(v_type_5732_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 1);
                    v___x_5733_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5664_, v_type_5732_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                    return v___x_5733_;
                }
                7 => {
                    v_fvarId_5734_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5734_);
                    v_y_5735_ = crate::leanh::lean_ctor_get(v_c_5665_, 2);
                    crate::leanh::lean_inc(v_y_5735_);
                    v_k_5736_ = crate::leanh::lean_ctor_get(v_c_5665_, 3);
                    crate::leanh::lean_inc_ref(v_k_5736_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 4);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5737_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5734_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5737_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5737_, 1);
                        crate::leanh::lean_inc_ref(v_f_5664_);
                        v___x_5738_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_5664_, v_y_5735_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                        if crate::leanh::lean_obj_tag(v___x_5738_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5738_, 1);
                            v_c_5665_ = v_k_5736_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5736_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            return v___x_5738_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5736_);
                        crate::leanh::lean_dec(v_y_5735_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5737_;
                    }
                }
                8 => {
                    v_fvarId_5740_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5740_);
                    v_y_5741_ = crate::leanh::lean_ctor_get(v_c_5665_, 2);
                    crate::leanh::lean_inc(v_y_5741_);
                    v_k_5742_ = crate::leanh::lean_ctor_get(v_c_5665_, 3);
                    crate::leanh::lean_inc_ref(v_k_5742_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 4);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5743_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5740_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5743_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5743_, 1);
                        crate::leanh::lean_inc_ref(v_f_5664_);
                        crate::leanh::lean_inc(v___y_5671_);
                        crate::leanh::lean_inc_ref(v___y_5670_);
                        crate::leanh::lean_inc(v___y_5669_);
                        crate::leanh::lean_inc_ref(v___y_5668_);
                        crate::leanh::lean_inc(v___y_5667_);
                        crate::leanh::lean_inc(v___y_5666_);
                        v___x_5744_ = crate::leanh::lean_apply_8(
                            v_f_5664_,
                            v_y_5741_,
                            v___y_5666_,
                            v___y_5667_,
                            v___y_5668_,
                            v___y_5669_,
                            v___y_5670_,
                            v___y_5671_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5744_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5744_, 1);
                            v_c_5665_ = v_k_5742_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5742_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            return v___x_5744_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5742_);
                        crate::leanh::lean_dec(v_y_5741_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5743_;
                    }
                }
                9 => {
                    v_fvarId_5746_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5746_);
                    v_y_5747_ = crate::leanh::lean_ctor_get(v_c_5665_, 3);
                    crate::leanh::lean_inc(v_y_5747_);
                    v_ty_5748_ = crate::leanh::lean_ctor_get(v_c_5665_, 4);
                    crate::leanh::lean_inc_ref(v_ty_5748_);
                    v_k_5749_ = crate::leanh::lean_ctor_get(v_c_5665_, 5);
                    crate::leanh::lean_inc_ref(v_k_5749_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 6);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5750_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5746_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5750_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5750_, 1);
                        crate::leanh::lean_inc_ref(v_f_5664_);
                        crate::leanh::lean_inc(v___y_5671_);
                        crate::leanh::lean_inc_ref(v___y_5670_);
                        crate::leanh::lean_inc(v___y_5669_);
                        crate::leanh::lean_inc_ref(v___y_5668_);
                        crate::leanh::lean_inc(v___y_5667_);
                        crate::leanh::lean_inc(v___y_5666_);
                        v___x_5751_ = crate::leanh::lean_apply_8(
                            v_f_5664_,
                            v_y_5747_,
                            v___y_5666_,
                            v___y_5667_,
                            v___y_5668_,
                            v___y_5669_,
                            v___y_5670_,
                            v___y_5671_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_5751_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5751_, 1);
                            crate::leanh::lean_inc_ref(v_f_5664_);
                            v___x_5752_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5664_, v_ty_5748_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                            if crate::leanh::lean_obj_tag(v___x_5752_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5752_, 1);
                                v_c_5665_ = v_k_5749_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_5749_);
                                crate::leanh::lean_dec_ref(v_f_5664_);
                                return v___x_5752_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_5749_);
                            crate::leanh::lean_dec_ref(v_ty_5748_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            return v___x_5751_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5749_);
                        crate::leanh::lean_dec_ref(v_ty_5748_);
                        crate::leanh::lean_dec(v_y_5747_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5750_;
                    }
                }
                10 => {
                    v_fvarId_5754_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5754_);
                    v_k_5755_ = crate::leanh::lean_ctor_get(v_c_5665_, 2);
                    crate::leanh::lean_inc_ref(v_k_5755_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 3);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5756_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5754_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5756_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5756_, 1);
                        v_c_5665_ = v_k_5755_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5755_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5756_;
                    }
                }
                11 => {
                    v_fvarId_5758_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5758_);
                    v_k_5759_ = crate::leanh::lean_ctor_get(v_c_5665_, 2);
                    crate::leanh::lean_inc_ref(v_k_5759_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 3);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5760_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5758_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5760_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5760_, 1);
                        v_c_5665_ = v_k_5759_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5759_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5760_;
                    }
                }
                12 => {
                    v_fvarId_5762_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5762_);
                    v_k_5763_ = crate::leanh::lean_ctor_get(v_c_5665_, 3);
                    crate::leanh::lean_inc_ref(v_k_5763_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 4);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5764_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5762_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5764_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5764_, 1);
                        v_c_5665_ = v_k_5763_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5763_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5764_;
                    }
                }
                13 => {
                    v_fvarId_5766_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc(v_fvarId_5766_);
                    v_k_5767_ = crate::leanh::lean_ctor_get(v_c_5665_, 1);
                    crate::leanh::lean_inc_ref(v_k_5767_);
                    crate::leanh::lean_dec_ref_known(v_c_5665_, 2);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    crate::leanh::lean_inc(v___y_5671_);
                    crate::leanh::lean_inc_ref(v___y_5670_);
                    crate::leanh::lean_inc(v___y_5669_);
                    crate::leanh::lean_inc_ref(v___y_5668_);
                    crate::leanh::lean_inc(v___y_5667_);
                    crate::leanh::lean_inc(v___y_5666_);
                    v___x_5768_ = crate::leanh::lean_apply_8(
                        v_f_5664_,
                        v_fvarId_5766_,
                        v___y_5666_,
                        v___y_5667_,
                        v___y_5668_,
                        v___y_5669_,
                        v___y_5670_,
                        v___y_5671_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5768_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5768_, 1);
                        v_c_5665_ = v_k_5767_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5767_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5768_;
                    }
                }
                _ => {
                    v_decl_5770_ = crate::leanh::lean_ctor_get(v_c_5665_, 0);
                    crate::leanh::lean_inc_ref(v_decl_5770_);
                    v_k_5771_ = crate::leanh::lean_ctor_get(v_c_5665_, 1);
                    crate::leanh::lean_inc_ref(v_k_5771_);
                    crate::leanh::lean_dec_ref(v_c_5665_);
                    v_params_5772_ = crate::leanh::lean_ctor_get(v_decl_5770_, 2);
                    crate::leanh::lean_inc_ref(v_params_5772_);
                    v_type_5773_ = crate::leanh::lean_ctor_get(v_decl_5770_, 3);
                    crate::leanh::lean_inc_ref(v_type_5773_);
                    v_value_5774_ = crate::leanh::lean_ctor_get(v_decl_5770_, 4);
                    crate::leanh::lean_inc_ref(v_value_5774_);
                    crate::leanh::lean_dec_ref(v_decl_5770_);
                    v___x_5785_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5786_ = lean_array_get_size(v_params_5772_);
                    v___x_5787_ = lean_nat_dec_lt(v___x_5785_, v___x_5786_);
                    if v___x_5787_ == 0 {
                        crate::leanh::lean_dec_ref(v_params_5772_);
                        crate::leanh::lean_inc_ref(v_f_5664_);
                        v___x_5788_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5664_, v_type_5773_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                        if crate::leanh::lean_obj_tag(v___x_5788_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5788_, 1);
                            crate::leanh::lean_inc_ref(v_f_5664_);
                            v___x_5789_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_5663_, v_f_5664_, v_value_5774_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                            if crate::leanh::lean_obj_tag(v___x_5789_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5789_, 1);
                                v_c_5665_ = v_k_5771_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_5771_);
                                crate::leanh::lean_dec_ref(v_f_5664_);
                                return v___x_5789_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_5774_);
                            crate::leanh::lean_dec_ref(v_k_5771_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            return v___x_5788_;
                        }
                    } else {
                        v___x_5791_ = crate::leanh::lean_box(0);
                        v___x_5792_ = lean_nat_dec_le(v___x_5786_, v___x_5786_);
                        if v___x_5792_ == 0 {
                            if v___x_5787_ == 0 {
                                crate::leanh::lean_dec_ref(v_params_5772_);
                                v___y_5776_ = v___y_5666_;
                                v___y_5777_ = v___y_5667_;
                                v___y_5778_ = v___y_5668_;
                                v___y_5779_ = v___y_5669_;
                                v___y_5780_ = v___y_5670_;
                                v___y_5781_ = v___y_5671_;
                                state = 7;
                                continue;
                            } else {
                                v___x_5793_ = 0usize;
                                v___x_5794_ = lean_usize_of_nat(v___x_5786_);
                                crate::leanh::lean_inc_ref(v_f_5664_);
                                v___x_5795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_5663_, v_f_5664_, v_params_5772_, v___x_5793_, v___x_5794_, v___x_5791_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                                crate::leanh::lean_dec_ref(v_params_5772_);
                                if crate::leanh::lean_obj_tag(v___x_5795_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5795_, 1);
                                    v___y_5776_ = v___y_5666_;
                                    v___y_5777_ = v___y_5667_;
                                    v___y_5778_ = v___y_5668_;
                                    v___y_5779_ = v___y_5669_;
                                    v___y_5780_ = v___y_5670_;
                                    v___y_5781_ = v___y_5671_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_value_5774_);
                                    crate::leanh::lean_dec_ref(v_type_5773_);
                                    crate::leanh::lean_dec_ref(v_k_5771_);
                                    crate::leanh::lean_dec_ref(v_f_5664_);
                                    return v___x_5795_;
                                }
                            }
                        } else {
                            v___x_5796_ = 0usize;
                            v___x_5797_ = lean_usize_of_nat(v___x_5786_);
                            crate::leanh::lean_inc_ref(v_f_5664_);
                            v___x_5798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__5(v_pu_5663_, v_f_5664_, v_params_5772_, v___x_5796_, v___x_5797_, v___x_5791_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                            crate::leanh::lean_dec_ref(v_params_5772_);
                            if crate::leanh::lean_obj_tag(v___x_5798_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5798_, 1);
                                v___y_5776_ = v___y_5666_;
                                v___y_5777_ = v___y_5667_;
                                v___y_5778_ = v___y_5668_;
                                v___y_5779_ = v___y_5669_;
                                v___y_5780_ = v___y_5670_;
                                v___y_5781_ = v___y_5671_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_value_5774_);
                                crate::leanh::lean_dec_ref(v_type_5773_);
                                crate::leanh::lean_dec_ref(v_k_5771_);
                                crate::leanh::lean_dec_ref(v_f_5664_);
                                return v___x_5798_;
                            }
                        }
                    }
                }
            },
            1 => {
                v___x_5683_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5684_ = lean_array_get_size(v_args_5678_);
                v___x_5685_ = crate::leanh::lean_box(0);
                v___x_5686_ = lean_nat_dec_lt(v___x_5683_, v___x_5684_);
                if v___x_5686_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_5678_);
                    crate::leanh::lean_dec_ref(v_f_5664_);
                    if v_isShared_5682_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5681_, 0, v___x_5685_);
                        v___x_5688_ = v___x_5681_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5689_, 0, v___x_5685_);
                        v___x_5688_ = v_reuseFailAlloc_5689_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5690_ = lean_nat_dec_le(v___x_5684_, v___x_5684_);
                    if v___x_5690_ == 0 {
                        if v___x_5686_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_5678_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            if v_isShared_5682_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5681_, 0, v___x_5685_);
                                v___x_5692_ = v___x_5681_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5693_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5693_, 0, v___x_5685_);
                                v___x_5692_ = v_reuseFailAlloc_5693_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5681_);
                            v___x_5694_ = 0usize;
                            v___x_5695_ = lean_usize_of_nat(v___x_5684_);
                            v___x_5696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5663_, v_f_5664_, v_args_5678_, v___x_5694_, v___x_5695_, v___x_5685_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                            crate::leanh::lean_dec_ref(v_args_5678_);
                            return v___x_5696_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5681_);
                        v___x_5697_ = 0usize;
                        v___x_5698_ = lean_usize_of_nat(v___x_5684_);
                        v___x_5699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__6(v_pu_5663_, v_f_5664_, v_args_5678_, v___x_5697_, v___x_5698_, v___x_5685_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                        crate::leanh::lean_dec_ref(v_args_5678_);
                        return v___x_5699_;
                    }
                }
            }
            2 => {
                return v___x_5688_;
            }
            3 => {
                return v___x_5692_;
            }
            4 => {
                v___x_5711_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5712_ = lean_array_get_size(v_alts_5705_);
                v___x_5713_ = crate::leanh::lean_box(0);
                v___x_5714_ = lean_nat_dec_lt(v___x_5711_, v___x_5712_);
                if v___x_5714_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_5705_);
                    crate::leanh::lean_dec_ref(v_f_5664_);
                    if v_isShared_5710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5709_, 0, v___x_5713_);
                        v___x_5716_ = v___x_5709_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5717_, 0, v___x_5713_);
                        v___x_5716_ = v_reuseFailAlloc_5717_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_5718_ = lean_nat_dec_le(v___x_5712_, v___x_5712_);
                    if v___x_5718_ == 0 {
                        if v___x_5714_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_5705_);
                            crate::leanh::lean_dec_ref(v_f_5664_);
                            if v_isShared_5710_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5709_, 0, v___x_5713_);
                                v___x_5720_ = v___x_5709_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_5721_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5713_);
                                v___x_5720_ = v_reuseFailAlloc_5721_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5709_);
                            v___x_5722_ = 0usize;
                            v___x_5723_ = lean_usize_of_nat(v___x_5712_);
                            v___x_5724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_5663_, v_f_5664_, v_alts_5705_, v___x_5722_, v___x_5723_, v___x_5713_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                            crate::leanh::lean_dec_ref(v_alts_5705_);
                            return v___x_5724_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5709_);
                        v___x_5725_ = 0usize;
                        v___x_5726_ = lean_usize_of_nat(v___x_5712_);
                        v___x_5727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_5663_, v_f_5664_, v_alts_5705_, v___x_5725_, v___x_5726_, v___x_5713_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
                        crate::leanh::lean_dec_ref(v_alts_5705_);
                        return v___x_5727_;
                    }
                }
            }
            5 => {
                return v___x_5716_;
            }
            6 => {
                return v___x_5720_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_f_5664_);
                v___x_5782_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(v_f_5664_, v_type_5773_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_);
                if crate::leanh::lean_obj_tag(v___x_5782_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5782_, 1);
                    crate::leanh::lean_inc_ref(v_f_5664_);
                    v___x_5783_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_5663_, v_f_5664_, v_value_5774_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_);
                    if crate::leanh::lean_obj_tag(v___x_5783_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5783_, 1);
                        v_c_5665_ = v_k_5771_;
                        v___y_5666_ = v___y_5776_;
                        v___y_5667_ = v___y_5777_;
                        v___y_5668_ = v___y_5778_;
                        v___y_5669_ = v___y_5779_;
                        v___y_5670_ = v___y_5780_;
                        v___y_5671_ = v___y_5781_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5771_);
                        crate::leanh::lean_dec_ref(v_f_5664_);
                        return v___x_5783_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_5774_);
                    crate::leanh::lean_dec_ref(v_k_5771_);
                    crate::leanh::lean_dec_ref(v_f_5664_);
                    return v___x_5782_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___lam__0(
    mut v_pu_5799_: u8,
    mut v_f_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
    mut v___y_5802_: *mut crate::leanh::LeanObject,
    mut v___y_5803_: *mut crate::leanh::LeanObject,
    mut v___y_5804_: *mut crate::leanh::LeanObject,
    mut v___y_5805_: *mut crate::leanh::LeanObject,
    mut v___y_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5809_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_5799_, v_f_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
    return v___x_5809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7___boxed(
    mut v_pu_5810_: *mut crate::leanh::LeanObject,
    mut v_f_5811_: *mut crate::leanh::LeanObject,
    mut v_as_5812_: *mut crate::leanh::LeanObject,
    mut v_i_5813_: *mut crate::leanh::LeanObject,
    mut v_stop_5814_: *mut crate::leanh::LeanObject,
    mut v_b_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
    mut v___y_5817_: *mut crate::leanh::LeanObject,
    mut v___y_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5823_: u8 = 0;
    let mut v_i_boxed_5824_: usize = 0;
    let mut v_stop_boxed_5825_: usize = 0;
    let mut v_res_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5823_ = (crate::leanh::lean_unbox(v_pu_5810_) as u8);
    v_i_boxed_5824_ = crate::leanh::lean_unbox_usize(v_i_5813_);
    crate::leanh::lean_dec(v_i_5813_);
    v_stop_boxed_5825_ = crate::leanh::lean_unbox_usize(v_stop_5814_);
    crate::leanh::lean_dec(v_stop_5814_);
    v_res_5826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__7(v_pu_boxed_5823_, v_f_5811_, v_as_5812_, v_i_boxed_5824_, v_stop_boxed_5825_, v_b_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
    crate::leanh::lean_dec(v___y_5821_);
    crate::leanh::lean_dec_ref(v___y_5820_);
    crate::leanh::lean_dec(v___y_5819_);
    crate::leanh::lean_dec_ref(v___y_5818_);
    crate::leanh::lean_dec(v___y_5817_);
    crate::leanh::lean_dec(v___y_5816_);
    crate::leanh::lean_dec_ref(v_as_5812_);
    return v_res_5826_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1___boxed(
    mut v_pu_5827_: *mut crate::leanh::LeanObject,
    mut v_f_5828_: *mut crate::leanh::LeanObject,
    mut v_c_5829_: *mut crate::leanh::LeanObject,
    mut v___y_5830_: *mut crate::leanh::LeanObject,
    mut v___y_5831_: *mut crate::leanh::LeanObject,
    mut v___y_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5837_: u8 = 0;
    let mut v_res_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5837_ = (crate::leanh::lean_unbox(v_pu_5827_) as u8);
    v_res_5838_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v_pu_boxed_5837_, v_f_5828_, v_c_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_);
    crate::leanh::lean_dec(v___y_5835_);
    crate::leanh::lean_dec_ref(v___y_5834_);
    crate::leanh::lean_dec(v___y_5833_);
    crate::leanh::lean_dec_ref(v___y_5832_);
    crate::leanh::lean_dec(v___y_5831_);
    crate::leanh::lean_dec(v___y_5830_);
    return v_res_5838_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(
    mut v___x_5839_: *mut crate::leanh::LeanObject,
    mut v_as_5840_: *mut crate::leanh::LeanObject,
    mut v_i_5841_: usize,
    mut v_stop_5842_: usize,
    mut v_b_5843_: *mut crate::leanh::LeanObject,
    mut v___y_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
    mut v___y_5847_: *mut crate::leanh::LeanObject,
    mut v___y_5848_: *mut crate::leanh::LeanObject,
    mut v___y_5849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5851_: u8 = 0;
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: usize = 0;
    let mut v___x_5857_: usize = 0;
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5851_ = lean_usize_dec_eq(v_i_5841_, v_stop_5842_);
                if v___x_5851_ == 0 {
                    crate::leanh::lean_inc(v___x_5839_);
                    v___x_5852_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed as *mut core::ffi::c_void, 9, 1);
                    crate::leanh::lean_closure_set(v___x_5852_, 0, v___x_5839_);
                    v___x_5853_ = lean_array_uget_borrowed(v_as_5840_, v_i_5841_);
                    crate::leanh::lean_inc(v___x_5853_);
                    v___x_5854_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v___x_5852_, v___x_5853_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_);
                    if crate::leanh::lean_obj_tag(v___x_5854_) == 0 {
                        v_a_5855_ = crate::leanh::lean_ctor_get(v___x_5854_, 0);
                        crate::leanh::lean_inc(v_a_5855_);
                        crate::leanh::lean_dec_ref_known(v___x_5854_, 1);
                        v___x_5856_ = 1usize;
                        v___x_5857_ = lean_usize_add(v_i_5841_, v___x_5856_);
                        v_i_5841_ = v___x_5857_;
                        v_b_5843_ = v_a_5855_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5839_);
                        return v___x_5854_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5839_);
                    v___x_5859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5859_, 0, v_b_5843_);
                    return v___x_5859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2___boxed(
    mut v___x_5860_: *mut crate::leanh::LeanObject,
    mut v_as_5861_: *mut crate::leanh::LeanObject,
    mut v_i_5862_: *mut crate::leanh::LeanObject,
    mut v_stop_5863_: *mut crate::leanh::LeanObject,
    mut v_b_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
    mut v___y_5867_: *mut crate::leanh::LeanObject,
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5872_: usize = 0;
    let mut v_stop_boxed_5873_: usize = 0;
    let mut v_res_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5872_ = crate::leanh::lean_unbox_usize(v_i_5862_);
    crate::leanh::lean_dec(v_i_5862_);
    v_stop_boxed_5873_ = crate::leanh::lean_unbox_usize(v_stop_5863_);
    crate::leanh::lean_dec(v_stop_5863_);
    v_res_5874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_5860_, v_as_5861_, v_i_boxed_5872_, v_stop_boxed_5873_, v_b_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
    crate::leanh::lean_dec(v___y_5870_);
    crate::leanh::lean_dec_ref(v___y_5869_);
    crate::leanh::lean_dec(v___y_5868_);
    crate::leanh::lean_dec_ref(v___y_5867_);
    crate::leanh::lean_dec(v___y_5866_);
    crate::leanh::lean_dec(v___y_5865_);
    crate::leanh::lean_dec_ref(v_as_5861_);
    return v_res_5874_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(
    mut v_alt_5875_: *mut crate::leanh::LeanObject,
    mut v_a_5876_: *mut crate::leanh::LeanObject,
    mut v_a_5877_: *mut crate::leanh::LeanObject,
    mut v_a_5878_: *mut crate::leanh::LeanObject,
    mut v_a_5879_: *mut crate::leanh::LeanObject,
    mut v_a_5880_: *mut crate::leanh::LeanObject,
    mut v_a_5881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5883_: u8 = 0;
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5883_ = 0;
    v___x_5884_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_alt_5875_);
    crate::leanh::lean_inc(v___x_5884_);
    v___x_5885_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed as *mut core::ffi::c_void, 9, 1);
    crate::leanh::lean_closure_set(v___x_5885_, 0, v___x_5884_);
    match crate::leanh::lean_obj_tag(v_alt_5875_) {
        0 => {
            let mut v_params_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_code_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5890_: u8 = 0;
            v_params_5886_ = crate::leanh::lean_ctor_get(v_alt_5875_, 1);
            crate::leanh::lean_inc_ref(v_params_5886_);
            v_code_5887_ = crate::leanh::lean_ctor_get(v_alt_5875_, 2);
            crate::leanh::lean_inc_ref(v_code_5887_);
            crate::leanh::lean_dec_ref_known(v_alt_5875_, 3);
            v___x_5888_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_5889_ = lean_array_get_size(v_params_5886_);
            v___x_5890_ = lean_nat_dec_lt(v___x_5888_, v___x_5889_);
            if v___x_5890_ == 0 {
                let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_params_5886_);
                crate::leanh::lean_dec(v___x_5884_);
                v___x_5891_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_5883_, v___x_5885_, v_code_5887_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
                return v___x_5891_;
            } else {
                let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5893_: u8 = 0;
                v___x_5892_ = crate::leanh::lean_box(0);
                v___x_5893_ = lean_nat_dec_le(v___x_5889_, v___x_5889_);
                if v___x_5893_ == 0 {
                    if v___x_5890_ == 0 {
                        let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref(v_params_5886_);
                        crate::leanh::lean_dec(v___x_5884_);
                        v___x_5894_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_5883_, v___x_5885_, v_code_5887_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
                        return v___x_5894_;
                    } else {
                        let mut v___x_5895_: usize = 0;
                        let mut v___x_5896_: usize = 0;
                        let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5895_ = 0usize;
                        v___x_5896_ = lean_usize_of_nat(v___x_5889_);
                        v___x_5897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_5884_, v_params_5886_, v___x_5895_, v___x_5896_, v___x_5892_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
                        crate::leanh::lean_dec_ref(v_params_5886_);
                        if crate::leanh::lean_obj_tag(v___x_5897_) == 0 {
                            let mut v___x_5898_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_5897_, 1);
                            v___x_5898_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_5883_, v___x_5885_, v_code_5887_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
                            return v___x_5898_;
                        } else {
                            crate::leanh::lean_dec_ref(v_code_5887_);
                            crate::leanh::lean_dec_ref(v___x_5885_);
                            return v___x_5897_;
                        }
                    }
                } else {
                    let mut v___x_5899_: usize = 0;
                    let mut v___x_5900_: usize = 0;
                    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_5899_ = 0usize;
                    v___x_5900_ = lean_usize_of_nat(v___x_5889_);
                    v___x_5901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__2(v___x_5884_, v_params_5886_, v___x_5899_, v___x_5900_, v___x_5892_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
                    crate::leanh::lean_dec_ref(v_params_5886_);
                    if crate::leanh::lean_obj_tag(v___x_5901_) == 0 {
                        let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_5901_, 1);
                        v___x_5902_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_5883_, v___x_5885_, v_code_5887_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
                        return v___x_5902_;
                    } else {
                        crate::leanh::lean_dec_ref(v_code_5887_);
                        crate::leanh::lean_dec_ref(v___x_5885_);
                        return v___x_5901_;
                    }
                }
            }
        }
        1 => {
            let mut v_code_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_5884_);
            v_code_5903_ = crate::leanh::lean_ctor_get(v_alt_5875_, 1);
            crate::leanh::lean_inc_ref(v_code_5903_);
            crate::leanh::lean_dec_ref_known(v_alt_5875_, 2);
            v___x_5904_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_5883_, v___x_5885_, v_code_5903_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
            return v___x_5904_;
        }
        _ => {
            let mut v_code_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_5884_);
            v_code_5905_ = crate::leanh::lean_ctor_get(v_alt_5875_, 0);
            crate::leanh::lean_inc_ref(v_code_5905_);
            crate::leanh::lean_dec_ref_known(v_alt_5875_, 1);
            v___x_5906_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1(v___x_5883_, v___x_5885_, v_code_5905_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_);
            return v___x_5906_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt___boxed(
    mut v_alt_5907_: *mut crate::leanh::LeanObject,
    mut v_a_5908_: *mut crate::leanh::LeanObject,
    mut v_a_5909_: *mut crate::leanh::LeanObject,
    mut v_a_5910_: *mut crate::leanh::LeanObject,
    mut v_a_5911_: *mut crate::leanh::LeanObject,
    mut v_a_5912_: *mut crate::leanh::LeanObject,
    mut v_a_5913_: *mut crate::leanh::LeanObject,
    mut v_a_5914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5915_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v_alt_5907_, v_a_5908_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_, v_a_5913_);
    crate::leanh::lean_dec(v_a_5913_);
    crate::leanh::lean_dec_ref(v_a_5912_);
    crate::leanh::lean_dec(v_a_5911_);
    crate::leanh::lean_dec_ref(v_a_5910_);
    crate::leanh::lean_dec(v_a_5909_);
    crate::leanh::lean_dec(v_a_5908_);
    return v_res_5915_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(
    mut v_pu_5916_: u8,
    mut v_f_5917_: *mut crate::leanh::LeanObject,
    mut v_param_5918_: *mut crate::leanh::LeanObject,
    mut v___y_5919_: *mut crate::leanh::LeanObject,
    mut v___y_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5926_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___redArg(v_f_5917_, v_param_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
    return v___x_5926_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0___boxed(
    mut v_pu_5927_: *mut crate::leanh::LeanObject,
    mut v_f_5928_: *mut crate::leanh::LeanObject,
    mut v_param_5929_: *mut crate::leanh::LeanObject,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
    mut v___y_5931_: *mut crate::leanh::LeanObject,
    mut v___y_5932_: *mut crate::leanh::LeanObject,
    mut v___y_5933_: *mut crate::leanh::LeanObject,
    mut v___y_5934_: *mut crate::leanh::LeanObject,
    mut v___y_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5937_: u8 = 0;
    let mut v_res_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5937_ = (crate::leanh::lean_unbox(v_pu_5927_) as u8);
    v_res_5938_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(v_pu_boxed_5937_, v_f_5928_, v_param_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
    crate::leanh::lean_dec(v___y_5935_);
    crate::leanh::lean_dec_ref(v___y_5934_);
    crate::leanh::lean_dec(v___y_5933_);
    crate::leanh::lean_dec_ref(v___y_5932_);
    crate::leanh::lean_dec(v___y_5931_);
    crate::leanh::lean_dec(v___y_5930_);
    return v_res_5938_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(
    mut v_pu_5939_: u8,
    mut v_alt_5940_: *mut crate::leanh::LeanObject,
    mut v_f_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
    mut v___y_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
    mut v___y_5947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5949_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___redArg(v_alt_5940_, v_f_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_);
    return v___x_5949_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3___boxed(
    mut v_pu_5950_: *mut crate::leanh::LeanObject,
    mut v_alt_5951_: *mut crate::leanh::LeanObject,
    mut v_f_5952_: *mut crate::leanh::LeanObject,
    mut v___y_5953_: *mut crate::leanh::LeanObject,
    mut v___y_5954_: *mut crate::leanh::LeanObject,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
    mut v___y_5958_: *mut crate::leanh::LeanObject,
    mut v___y_5959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5960_: u8 = 0;
    let mut v_res_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5960_ = (crate::leanh::lean_unbox(v_pu_5950_) as u8);
    v_res_5961_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__3(v_pu_boxed_5960_, v_alt_5951_, v_f_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_);
    crate::leanh::lean_dec(v___y_5958_);
    crate::leanh::lean_dec_ref(v___y_5957_);
    crate::leanh::lean_dec(v___y_5956_);
    crate::leanh::lean_dec_ref(v___y_5955_);
    crate::leanh::lean_dec(v___y_5954_);
    crate::leanh::lean_dec(v___y_5953_);
    return v_res_5961_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(
    mut v_pu_5962_: u8,
    mut v_f_5963_: *mut crate::leanh::LeanObject,
    mut v_arg_5964_: *mut crate::leanh::LeanObject,
    mut v___y_5965_: *mut crate::leanh::LeanObject,
    mut v___y_5966_: *mut crate::leanh::LeanObject,
    mut v___y_5967_: *mut crate::leanh::LeanObject,
    mut v___y_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5972_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___redArg(v_f_5963_, v_arg_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_);
    return v___x_5972_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2___boxed(
    mut v_pu_5973_: *mut crate::leanh::LeanObject,
    mut v_f_5974_: *mut crate::leanh::LeanObject,
    mut v_arg_5975_: *mut crate::leanh::LeanObject,
    mut v___y_5976_: *mut crate::leanh::LeanObject,
    mut v___y_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_5983_: u8 = 0;
    let mut v_res_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_5983_ = (crate::leanh::lean_unbox(v_pu_5973_) as u8);
    v_res_5984_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__1_spec__2(v_pu_boxed_5983_, v_f_5974_, v_arg_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_);
    crate::leanh::lean_dec(v___y_5981_);
    crate::leanh::lean_dec_ref(v___y_5980_);
    crate::leanh::lean_dec(v___y_5979_);
    crate::leanh::lean_dec_ref(v___y_5978_);
    crate::leanh::lean_dec(v___y_5977_);
    crate::leanh::lean_dec(v___y_5976_);
    return v_res_5984_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(
    mut v_as_5985_: *mut crate::leanh::LeanObject,
    mut v_i_5986_: usize,
    mut v_stop_5987_: usize,
    mut v_b_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5996_: u8 = 0;
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: usize = 0;
    let mut v___x_6001_: usize = 0;
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5996_ = lean_usize_dec_eq(v_i_5986_, v_stop_5987_);
                if v___x_5996_ == 0 {
                    v___x_5997_ = lean_array_uget_borrowed(v_as_5985_, v_i_5986_);
                    crate::leanh::lean_inc(v___x_5997_);
                    v___x_5998_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(v___x_5997_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
                    if crate::leanh::lean_obj_tag(v___x_5998_) == 0 {
                        v_a_5999_ = crate::leanh::lean_ctor_get(v___x_5998_, 0);
                        crate::leanh::lean_inc(v_a_5999_);
                        crate::leanh::lean_dec_ref_known(v___x_5998_, 1);
                        v___x_6000_ = 1usize;
                        v___x_6001_ = lean_usize_add(v_i_5986_, v___x_6000_);
                        v_i_5986_ = v___x_6001_;
                        v_b_5988_ = v_a_5999_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5998_;
                    }
                } else {
                    v___x_6003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6003_, 0, v_b_5988_);
                    return v___x_6003_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(
    mut v_as_6004_: *mut crate::leanh::LeanObject,
    mut v_i_6005_: *mut crate::leanh::LeanObject,
    mut v_stop_6006_: *mut crate::leanh::LeanObject,
    mut v_b_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
    mut v___y_6012_: *mut crate::leanh::LeanObject,
    mut v___y_6013_: *mut crate::leanh::LeanObject,
    mut v___y_6014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6015_: usize = 0;
    let mut v_stop_boxed_6016_: usize = 0;
    let mut v_res_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6015_ = crate::leanh::lean_unbox_usize(v_i_6005_);
    crate::leanh::lean_dec(v_i_6005_);
    v_stop_boxed_6016_ = crate::leanh::lean_unbox_usize(v_stop_6006_);
    crate::leanh::lean_dec(v_stop_6006_);
    v_res_6017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_as_6004_, v_i_boxed_6015_, v_stop_boxed_6016_, v_b_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_);
    crate::leanh::lean_dec(v___y_6013_);
    crate::leanh::lean_dec_ref(v___y_6012_);
    crate::leanh::lean_dec(v___y_6011_);
    crate::leanh::lean_dec_ref(v___y_6010_);
    crate::leanh::lean_dec(v___y_6009_);
    crate::leanh::lean_dec(v___y_6008_);
    crate::leanh::lean_dec_ref(v_as_6004_);
    return v_res_6017_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(
    mut v_cs_6018_: *mut crate::leanh::LeanObject,
    mut v_a_6019_: *mut crate::leanh::LeanObject,
    mut v_a_6020_: *mut crate::leanh::LeanObject,
    mut v_a_6021_: *mut crate::leanh::LeanObject,
    mut v_a_6022_: *mut crate::leanh::LeanObject,
    mut v_a_6023_: *mut crate::leanh::LeanObject,
    mut v_a_6024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_alts_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: u8 = 0;
    v_alts_6026_ = crate::leanh::lean_ctor_get(v_cs_6018_, 3);
    v___x_6027_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6028_ = lean_array_get_size(v_alts_6026_);
    v___x_6029_ = crate::leanh::lean_box(0);
    v___x_6030_ = lean_nat_dec_lt(v___x_6027_, v___x_6028_);
    if v___x_6030_ == 0 {
        let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6031_, 0, v___x_6029_);
        return v___x_6031_;
    } else {
        let mut v___x_6032_: u8 = 0;
        v___x_6032_ = lean_nat_dec_le(v___x_6028_, v___x_6028_);
        if v___x_6032_ == 0 {
            if v___x_6030_ == 0 {
                let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6033_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6033_, 0, v___x_6029_);
                return v___x_6033_;
            } else {
                let mut v___x_6034_: usize = 0;
                let mut v___x_6035_: usize = 0;
                let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6034_ = 0usize;
                v___x_6035_ = lean_usize_of_nat(v___x_6028_);
                v___x_6036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_6026_, v___x_6034_, v___x_6035_, v___x_6029_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_);
                return v___x_6036_;
            }
        } else {
            let mut v___x_6037_: usize = 0;
            let mut v___x_6038_: usize = 0;
            let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6037_ = 0usize;
            v___x_6038_ = lean_usize_of_nat(v___x_6028_);
            v___x_6039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(v_alts_6026_, v___x_6037_, v___x_6038_, v___x_6029_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_, v_a_6024_);
            return v___x_6039_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(
    mut v_cs_6040_: *mut crate::leanh::LeanObject,
    mut v_a_6041_: *mut crate::leanh::LeanObject,
    mut v_a_6042_: *mut crate::leanh::LeanObject,
    mut v_a_6043_: *mut crate::leanh::LeanObject,
    mut v_a_6044_: *mut crate::leanh::LeanObject,
    mut v_a_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v_a_6047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6048_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_6040_, v_a_6041_, v_a_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_);
    crate::leanh::lean_dec(v_a_6046_);
    crate::leanh::lean_dec_ref(v_a_6045_);
    crate::leanh::lean_dec(v_a_6044_);
    crate::leanh::lean_dec_ref(v_a_6043_);
    crate::leanh::lean_dec(v_a_6042_);
    crate::leanh::lean_dec(v_a_6041_);
    crate::leanh::lean_dec_ref(v_cs_6040_);
    return v_res_6048_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(
    mut v_x_6049_: *mut crate::leanh::LeanObject,
    mut v_x_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
    mut v___y_6053_: *mut crate::leanh::LeanObject,
    mut v___y_6054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v_fst_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6066_: u8 = 0;
    let mut v___y_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: u8 = 0;
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_decl_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: u8 = 0;
    let mut v_fvarId_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6118_: u8 = 0;
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_isSharedCheck_6120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6050_) == 0 {
                    v___x_6056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6056_, 0, v_x_6049_);
                    return v___x_6056_;
                } else {
                    v_head_6057_ = crate::leanh::lean_ctor_get(v_x_6050_, 0);
                    v_tail_6058_ = crate::leanh::lean_ctor_get(v_x_6050_, 1);
                    v_isSharedCheck_6120_ = (!crate::leanh::lean_is_exclusive(v_x_6050_)) as u8;
                    if v_isSharedCheck_6120_ == 0 {
                        v___x_6060_ = v_x_6050_;
                        v_isShared_6061_ = v_isSharedCheck_6120_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6058_);
                        crate::leanh::lean_inc(v_head_6057_);
                        crate::leanh::lean_dec(v_x_6050_);
                        v___x_6060_ = crate::leanh::lean_box(0);
                        v_isShared_6061_ = v_isSharedCheck_6120_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6062_ = crate::leanh::lean_ctor_get(v_x_6049_, 0);
                v_snd_6063_ = crate::leanh::lean_ctor_get(v_x_6049_, 1);
                v_isSharedCheck_6119_ = (!crate::leanh::lean_is_exclusive(v_x_6049_)) as u8;
                if v_isSharedCheck_6119_ == 0 {
                    v___x_6065_ = v_x_6049_;
                    v_isShared_6066_ = v_isSharedCheck_6119_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6063_);
                    crate::leanh::lean_inc(v_fst_6062_);
                    crate::leanh::lean_dec(v_x_6049_);
                    v___x_6065_ = crate::leanh::lean_box(0);
                    v_isShared_6066_ = v_isSharedCheck_6119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_head_6057_) == 0 {
                    v_decl_6100_ = crate::leanh::lean_ctor_get(v_head_6057_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6100_);
                    v___x_6101_ = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(
                        v_decl_6100_,
                        v___y_6051_,
                        v___y_6052_,
                        v___y_6053_,
                        v___y_6054_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6101_) == 0 {
                        v_a_6102_ = crate::leanh::lean_ctor_get(v___x_6101_, 0);
                        crate::leanh::lean_inc(v_a_6102_);
                        crate::leanh::lean_dec_ref_known(v___x_6101_, 1);
                        v___x_6103_ = (crate::leanh::lean_unbox(v_a_6102_) as u8);
                        crate::leanh::lean_dec(v_a_6102_);
                        if v___x_6103_ == 0 {
                            crate::leanh::lean_del_object(v___x_6060_);
                            v___y_6068_ = v___y_6051_;
                            v___y_6069_ = v___y_6052_;
                            v___y_6070_ = v___y_6053_;
                            v___y_6071_ = v___y_6054_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_decl_6100_);
                            crate::leanh::lean_dec_ref_known(v_head_6057_, 1);
                            crate::leanh::lean_del_object(v___x_6065_);
                            v_fvarId_6104_ = crate::leanh::lean_ctor_get(v_decl_6100_, 0);
                            crate::leanh::lean_inc(v_fvarId_6104_);
                            crate::leanh::lean_dec_ref(v_decl_6100_);
                            v___x_6105_ = crate::leanh::lean_box(2);
                            v___x_6106_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_6062_, v_fvarId_6104_, v___x_6105_);
                            if v_isShared_6061_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6060_, 0);
                                crate::leanh::lean_ctor_set(v___x_6060_, 1, v_snd_6063_);
                                crate::leanh::lean_ctor_set(v___x_6060_, 0, v___x_6106_);
                                v___x_6108_ = v___x_6060_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_6110_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6110_, 0, v___x_6106_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6110_, 1, v_snd_6063_);
                                v___x_6108_ = v_reuseFailAlloc_6110_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_head_6057_, 1);
                        crate::leanh::lean_del_object(v___x_6065_);
                        crate::leanh::lean_dec(v_snd_6063_);
                        crate::leanh::lean_dec(v_fst_6062_);
                        crate::leanh::lean_del_object(v___x_6060_);
                        crate::leanh::lean_dec(v_tail_6058_);
                        v_a_6111_ = crate::leanh::lean_ctor_get(v___x_6101_, 0);
                        v_isSharedCheck_6118_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6101_)) as u8;
                        if v_isSharedCheck_6118_ == 0 {
                            v___x_6113_ = v___x_6101_;
                            v_isShared_6114_ = v_isSharedCheck_6118_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6111_);
                            crate::leanh::lean_dec(v___x_6101_);
                            v___x_6113_ = crate::leanh::lean_box(0);
                            v_isShared_6114_ = v_isSharedCheck_6118_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6060_);
                    v___y_6068_ = v___y_6051_;
                    v___y_6069_ = v___y_6052_;
                    v___y_6070_ = v___y_6053_;
                    v___y_6071_ = v___y_6054_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6072_ = lean_st_ref_get(v___y_6071_);
                crate::leanh::lean_dec(v___x_6072_);
                v___x_6073_ = lean_st_mk_ref(v_snd_6063_);
                crate::leanh::lean_inc(v_head_6057_);
                v___x_6074_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitDecl___redArg(v_head_6057_, v___x_6073_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_);
                if crate::leanh::lean_obj_tag(v___x_6074_) == 0 {
                    v_a_6075_ = crate::leanh::lean_ctor_get(v___x_6074_, 0);
                    crate::leanh::lean_inc(v_a_6075_);
                    crate::leanh::lean_dec_ref_known(v___x_6074_, 1);
                    v___x_6076_ = lean_st_ref_get(v___x_6073_);
                    crate::leanh::lean_dec(v___x_6073_);
                    v___x_6077_ = (crate::leanh::lean_unbox(v_a_6075_) as u8);
                    crate::leanh::lean_dec(v_a_6075_);
                    if v___x_6077_ == 0 {
                        v___x_6078_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_6057_);
                        crate::leanh::lean_dec(v_head_6057_);
                        v___x_6079_ = crate::leanh::lean_box(3);
                        v___x_6080_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_6062_, v___x_6078_, v___x_6079_);
                        if v_isShared_6066_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6065_, 1, v___x_6076_);
                            crate::leanh::lean_ctor_set(v___x_6065_, 0, v___x_6080_);
                            v___x_6082_ = v___x_6065_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6084_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 0, v___x_6080_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 1, v___x_6076_);
                            v___x_6082_ = v_reuseFailAlloc_6084_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_6085_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_6057_);
                        crate::leanh::lean_dec(v_head_6057_);
                        v___x_6086_ = crate::leanh::lean_box(2);
                        v___x_6087_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_6062_, v___x_6085_, v___x_6086_);
                        if v_isShared_6066_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6065_, 1, v___x_6076_);
                            crate::leanh::lean_ctor_set(v___x_6065_, 0, v___x_6087_);
                            v___x_6089_ = v___x_6065_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_6091_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6091_, 0, v___x_6087_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6091_, 1, v___x_6076_);
                            v___x_6089_ = v_reuseFailAlloc_6091_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6073_);
                    crate::leanh::lean_del_object(v___x_6065_);
                    crate::leanh::lean_dec(v_fst_6062_);
                    crate::leanh::lean_dec(v_tail_6058_);
                    crate::leanh::lean_dec(v_head_6057_);
                    v_a_6092_ = crate::leanh::lean_ctor_get(v___x_6074_, 0);
                    v_isSharedCheck_6099_ = (!crate::leanh::lean_is_exclusive(v___x_6074_)) as u8;
                    if v_isSharedCheck_6099_ == 0 {
                        v___x_6094_ = v___x_6074_;
                        v_isShared_6095_ = v_isSharedCheck_6099_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6092_);
                        crate::leanh::lean_dec(v___x_6074_);
                        v___x_6094_ = crate::leanh::lean_box(0);
                        v_isShared_6095_ = v_isSharedCheck_6099_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v_x_6049_ = v___x_6082_;
                v_x_6050_ = v_tail_6058_;
                state = 0;
                continue;
            }
            5 => {
                v_x_6049_ = v___x_6089_;
                v_x_6050_ = v_tail_6058_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6095_ == 0 {
                    v___x_6097_ = v___x_6094_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
                    v___x_6097_ = v_reuseFailAlloc_6098_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6097_;
            }
            8 => {
                v_x_6049_ = v___x_6108_;
                v_x_6050_ = v_tail_6058_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_6114_ == 0 {
                    v___x_6116_ = v___x_6113_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
                    v___x_6116_ = v_reuseFailAlloc_6117_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(
    mut v_x_6121_: *mut crate::leanh::LeanObject,
    mut v_x_6122_: *mut crate::leanh::LeanObject,
    mut v___y_6123_: *mut crate::leanh::LeanObject,
    mut v___y_6124_: *mut crate::leanh::LeanObject,
    mut v___y_6125_: *mut crate::leanh::LeanObject,
    mut v___y_6126_: *mut crate::leanh::LeanObject,
    mut v___y_6127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6128_ =
        l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(
            v_x_6121_,
            v_x_6122_,
            v___y_6123_,
            v___y_6124_,
            v___y_6125_,
            v___y_6126_,
        );
    crate::leanh::lean_dec(v___y_6126_);
    crate::leanh::lean_dec_ref(v___y_6125_);
    crate::leanh::lean_dec(v___y_6124_);
    crate::leanh::lean_dec_ref(v___y_6123_);
    return v_res_6128_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6129_ = crate::leanh::lean_box(0);
    v___x_6130_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_6131_ = lean_mk_array(v___x_6130_, v___x_6129_);
    return v___x_6131_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6132_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0_once),
        _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__0,
    );
    v___x_6133_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6134_, 0, v___x_6133_);
    crate::leanh::lean_ctor_set(v___x_6134_, 1, v___x_6132_);
    return v___x_6134_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(
    mut v_cs_6135_: *mut crate::leanh::LeanObject,
    mut v_a_6136_: *mut crate::leanh::LeanObject,
    mut v_a_6137_: *mut crate::leanh::LeanObject,
    mut v_a_6138_: *mut crate::leanh::LeanObject,
    mut v_a_6139_: *mut crate::leanh::LeanObject,
    mut v_a_6140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6158_: u8 = 0;
    let mut v_unused_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: u8 = 0;
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6190_: u8 = 0;
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6168_ = l_List_lengthTR___redArg(v_a_6136_);
                v___x_6169_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6170_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_6171_ = lean_nat_mul(v___x_6168_, v___x_6170_);
                crate::leanh::lean_dec(v___x_6168_);
                v___x_6172_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6173_ = lean_nat_div(v___x_6171_, v___x_6172_);
                crate::leanh::lean_dec(v___x_6171_);
                v___x_6174_ = l_Nat_nextPowerOfTwo(v___x_6173_);
                crate::leanh::lean_dec(v___x_6173_);
                v___x_6175_ = crate::leanh::lean_box(0);
                v___x_6176_ = lean_mk_array(v___x_6174_, v___x_6175_);
                v___x_6177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6177_, 0, v___x_6169_);
                crate::leanh::lean_ctor_set(v___x_6177_, 1, v___x_6176_);
                v___x_6178_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___closed__1,
                );
                v___x_6179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6179_, 0, v___x_6177_);
                crate::leanh::lean_ctor_set(v___x_6179_, 1, v___x_6178_);
                crate::leanh::lean_inc(v_a_6136_);
                v___x_6180_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(v___x_6179_, v_a_6136_, v_a_6137_, v_a_6138_, v_a_6139_, v_a_6140_);
                if crate::leanh::lean_obj_tag(v___x_6180_) == 0 {
                    v_a_6181_ = crate::leanh::lean_ctor_get(v___x_6180_, 0);
                    crate::leanh::lean_inc(v_a_6181_);
                    crate::leanh::lean_dec_ref_known(v___x_6180_, 1);
                    v_fst_6182_ = crate::leanh::lean_ctor_get(v_a_6181_, 0);
                    crate::leanh::lean_inc(v_fst_6182_);
                    crate::leanh::lean_dec(v_a_6181_);
                    v_discr_6183_ = crate::leanh::lean_ctor_get(v_cs_6135_, 2);
                    v___x_6184_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_fst_6182_, v_discr_6183_);
                    if v___x_6184_ == 0 {
                        v_map_6143_ = v_fst_6182_;
                        v___y_6144_ = v_a_6136_;
                        v___y_6145_ = v_a_6137_;
                        v___y_6146_ = v_a_6138_;
                        v___y_6147_ = v_a_6139_;
                        v___y_6148_ = v_a_6140_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6185_ = crate::leanh::lean_box(2);
                        crate::leanh::lean_inc(v_discr_6183_);
                        v___x_6186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_fst_6182_, v_discr_6183_, v___x_6185_);
                        v_map_6143_ = v___x_6186_;
                        v___y_6144_ = v_a_6136_;
                        v___y_6145_ = v_a_6137_;
                        v___y_6146_ = v_a_6138_;
                        v___y_6147_ = v_a_6139_;
                        v___y_6148_ = v_a_6140_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cs_6135_);
                    v_a_6187_ = crate::leanh::lean_ctor_get(v___x_6180_, 0);
                    v_isSharedCheck_6194_ = (!crate::leanh::lean_is_exclusive(v___x_6180_)) as u8;
                    if v_isSharedCheck_6194_ == 0 {
                        v___x_6189_ = v___x_6180_;
                        v_isShared_6190_ = v_isSharedCheck_6194_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6187_);
                        crate::leanh::lean_dec(v___x_6180_);
                        v___x_6189_ = crate::leanh::lean_box(0);
                        v_isShared_6190_ = v_isSharedCheck_6194_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6149_ = lean_st_mk_ref(v_map_6143_);
                v___x_6150_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(v_cs_6135_, v___x_6149_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
                crate::leanh::lean_dec_ref(v_cs_6135_);
                if crate::leanh::lean_obj_tag(v___x_6150_) == 0 {
                    v_isSharedCheck_6158_ = (!crate::leanh::lean_is_exclusive(v___x_6150_)) as u8;
                    if v_isSharedCheck_6158_ == 0 {
                        v_unused_6159_ = crate::leanh::lean_ctor_get(v___x_6150_, 0);
                        crate::leanh::lean_dec(v_unused_6159_);
                        v___x_6152_ = v___x_6150_;
                        v_isShared_6153_ = v_isSharedCheck_6158_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6150_);
                        v___x_6152_ = crate::leanh::lean_box(0);
                        v_isShared_6153_ = v_isSharedCheck_6158_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6149_);
                    v_a_6160_ = crate::leanh::lean_ctor_get(v___x_6150_, 0);
                    v_isSharedCheck_6167_ = (!crate::leanh::lean_is_exclusive(v___x_6150_)) as u8;
                    if v_isSharedCheck_6167_ == 0 {
                        v___x_6162_ = v___x_6150_;
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6160_);
                        crate::leanh::lean_dec(v___x_6150_);
                        v___x_6162_ = crate::leanh::lean_box(0);
                        v_isShared_6163_ = v_isSharedCheck_6167_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6154_ = lean_st_ref_get(v___x_6149_);
                crate::leanh::lean_dec(v___x_6149_);
                if v_isShared_6153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6152_, 0, v___x_6154_);
                    v___x_6156_ = v___x_6152_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
                    v___x_6156_ = v_reuseFailAlloc_6157_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6156_;
            }
            4 => {
                if v_isShared_6163_ == 0 {
                    v___x_6165_ = v___x_6162_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
                    v___x_6165_ = v_reuseFailAlloc_6166_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6165_;
            }
            6 => {
                if v_isShared_6190_ == 0 {
                    v___x_6192_ = v___x_6189_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 0, v_a_6187_);
                    v___x_6192_ = v_reuseFailAlloc_6193_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions___boxed(
    mut v_cs_6195_: *mut crate::leanh::LeanObject,
    mut v_a_6196_: *mut crate::leanh::LeanObject,
    mut v_a_6197_: *mut crate::leanh::LeanObject,
    mut v_a_6198_: *mut crate::leanh::LeanObject,
    mut v_a_6199_: *mut crate::leanh::LeanObject,
    mut v_a_6200_: *mut crate::leanh::LeanObject,
    mut v_a_6201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6202_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(
        v_cs_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, v_a_6200_,
    );
    crate::leanh::lean_dec(v_a_6200_);
    crate::leanh::lean_dec_ref(v_a_6199_);
    crate::leanh::lean_dec(v_a_6198_);
    crate::leanh::lean_dec_ref(v_a_6197_);
    crate::leanh::lean_dec(v_a_6196_);
    return v_res_6202_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(
    mut v_x_6203_: *mut crate::leanh::LeanObject,
    mut v_x_6204_: *mut crate::leanh::LeanObject,
    mut v___y_6205_: *mut crate::leanh::LeanObject,
    mut v___y_6206_: *mut crate::leanh::LeanObject,
    mut v___y_6207_: *mut crate::leanh::LeanObject,
    mut v___y_6208_: *mut crate::leanh::LeanObject,
    mut v___y_6209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6211_ =
        l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(
            v_x_6203_,
            v_x_6204_,
            v___y_6206_,
            v___y_6207_,
            v___y_6208_,
            v___y_6209_,
        );
    return v___x_6211_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(
    mut v_x_6212_: *mut crate::leanh::LeanObject,
    mut v_x_6213_: *mut crate::leanh::LeanObject,
    mut v___y_6214_: *mut crate::leanh::LeanObject,
    mut v___y_6215_: *mut crate::leanh::LeanObject,
    mut v___y_6216_: *mut crate::leanh::LeanObject,
    mut v___y_6217_: *mut crate::leanh::LeanObject,
    mut v___y_6218_: *mut crate::leanh::LeanObject,
    mut v___y_6219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6220_ = l_List_foldlM___at___00Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(
        v_x_6212_,
        v_x_6213_,
        v___y_6214_,
        v___y_6215_,
        v___y_6216_,
        v___y_6217_,
        v___y_6218_,
    );
    crate::leanh::lean_dec(v___y_6218_);
    crate::leanh::lean_dec_ref(v___y_6217_);
    crate::leanh::lean_dec(v___y_6216_);
    crate::leanh::lean_dec_ref(v___y_6215_);
    crate::leanh::lean_dec(v___y_6214_);
    return v_res_6220_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(
    mut v_a_6221_: *mut crate::leanh::LeanObject,
    mut v_x_6222_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6223_: u8 = 0;
    let mut v_key_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6222_) == 0 {
                    v___x_6223_ = 0;
                    return v___x_6223_;
                } else {
                    v_key_6224_ = crate::leanh::lean_ctor_get(v_x_6222_, 0);
                    v_tail_6225_ = crate::leanh::lean_ctor_get(v_x_6222_, 2);
                    v___x_6226_ =
                        l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_6224_, v_a_6221_);
                    if v___x_6226_ == 0 {
                        v_x_6222_ = v_tail_6225_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6226_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg___boxed(
    mut v_a_6228_: *mut crate::leanh::LeanObject,
    mut v_x_6229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6230_: u8 = 0;
    let mut v_r_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6230_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_6228_, v_x_6229_);
    crate::leanh::lean_dec(v_x_6229_);
    crate::leanh::lean_dec(v_a_6228_);
    v_r_6231_ = crate::leanh::lean_box((v_res_6230_) as usize);
    return v_r_6231_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(
    mut v_a_6232_: *mut crate::leanh::LeanObject,
    mut v_b_6233_: *mut crate::leanh::LeanObject,
    mut v_x_6234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6240_: u8 = 0;
    let mut v___x_6241_: u8 = 0;
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6234_) == 0 {
                    crate::leanh::lean_dec(v_b_6233_);
                    crate::leanh::lean_dec(v_a_6232_);
                    return v_x_6234_;
                } else {
                    v_key_6235_ = crate::leanh::lean_ctor_get(v_x_6234_, 0);
                    v_value_6236_ = crate::leanh::lean_ctor_get(v_x_6234_, 1);
                    v_tail_6237_ = crate::leanh::lean_ctor_get(v_x_6234_, 2);
                    v_isSharedCheck_6249_ = (!crate::leanh::lean_is_exclusive(v_x_6234_)) as u8;
                    if v_isSharedCheck_6249_ == 0 {
                        v___x_6239_ = v_x_6234_;
                        v_isShared_6240_ = v_isSharedCheck_6249_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6237_);
                        crate::leanh::lean_inc(v_value_6236_);
                        crate::leanh::lean_inc(v_key_6235_);
                        crate::leanh::lean_dec(v_x_6234_);
                        v___x_6239_ = crate::leanh::lean_box(0);
                        v_isShared_6240_ = v_isSharedCheck_6249_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6241_ =
                    l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_6235_, v_a_6232_);
                if v___x_6241_ == 0 {
                    v___x_6242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_6232_, v_b_6233_, v_tail_6237_);
                    if v_isShared_6240_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6239_, 2, v___x_6242_);
                        v___x_6244_ = v___x_6239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6245_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6245_, 0, v_key_6235_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6245_, 1, v_value_6236_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6245_, 2, v___x_6242_);
                        v___x_6244_ = v_reuseFailAlloc_6245_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_6236_);
                    crate::leanh::lean_dec(v_key_6235_);
                    if v_isShared_6240_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6239_, 1, v_b_6233_);
                        crate::leanh::lean_ctor_set(v___x_6239_, 0, v_a_6232_);
                        v___x_6247_ = v___x_6239_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6248_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6232_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6248_, 1, v_b_6233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6248_, 2, v_tail_6237_);
                        v___x_6247_ = v_reuseFailAlloc_6248_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6244_;
            }
            3 => {
                return v___x_6247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_6250_: *mut crate::leanh::LeanObject,
    mut v_x_6251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: u64 = 0;
    let mut v___x_6260_: u64 = 0;
    let mut v___x_6261_: u64 = 0;
    let mut v_fold_6262_: u64 = 0;
    let mut v___x_6263_: u64 = 0;
    let mut v___x_6264_: u64 = 0;
    let mut v___x_6265_: u64 = 0;
    let mut v___x_6266_: usize = 0;
    let mut v___x_6267_: usize = 0;
    let mut v___x_6268_: usize = 0;
    let mut v___x_6269_: usize = 0;
    let mut v___x_6270_: usize = 0;
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6251_) == 0 {
                    return v_x_6250_;
                } else {
                    v_key_6252_ = crate::leanh::lean_ctor_get(v_x_6251_, 0);
                    v_value_6253_ = crate::leanh::lean_ctor_get(v_x_6251_, 1);
                    v_tail_6254_ = crate::leanh::lean_ctor_get(v_x_6251_, 2);
                    v_isSharedCheck_6277_ = (!crate::leanh::lean_is_exclusive(v_x_6251_)) as u8;
                    if v_isSharedCheck_6277_ == 0 {
                        v___x_6256_ = v_x_6251_;
                        v_isShared_6257_ = v_isSharedCheck_6277_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6254_);
                        crate::leanh::lean_inc(v_value_6253_);
                        crate::leanh::lean_inc(v_key_6252_);
                        crate::leanh::lean_dec(v_x_6251_);
                        v___x_6256_ = crate::leanh::lean_box(0);
                        v_isShared_6257_ = v_isSharedCheck_6277_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6258_ = lean_array_get_size(v_x_6250_);
                v___x_6259_ =
                    l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_key_6252_);
                v___x_6260_ = 32u64;
                v___x_6261_ = lean_uint64_shift_right(v___x_6259_, v___x_6260_);
                v_fold_6262_ = lean_uint64_xor(v___x_6259_, v___x_6261_);
                v___x_6263_ = 16u64;
                v___x_6264_ = lean_uint64_shift_right(v_fold_6262_, v___x_6263_);
                v___x_6265_ = lean_uint64_xor(v_fold_6262_, v___x_6264_);
                v___x_6266_ = lean_uint64_to_usize(v___x_6265_);
                v___x_6267_ = lean_usize_of_nat(v___x_6258_);
                v___x_6268_ = 1usize;
                v___x_6269_ = lean_usize_sub(v___x_6267_, v___x_6268_);
                v___x_6270_ = lean_usize_land(v___x_6266_, v___x_6269_);
                v___x_6271_ = lean_array_uget_borrowed(v_x_6250_, v___x_6270_);
                crate::leanh::lean_inc(v___x_6271_);
                if v_isShared_6257_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6256_, 2, v___x_6271_);
                    v___x_6273_ = v___x_6256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_key_6252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 1, v_value_6253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6276_, 2, v___x_6271_);
                    v___x_6273_ = v_reuseFailAlloc_6276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6274_ = lean_array_uset(v_x_6250_, v___x_6270_, v___x_6273_);
                v_x_6250_ = v___x_6274_;
                v_x_6251_ = v_tail_6254_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(
    mut v_i_6278_: *mut crate::leanh::LeanObject,
    mut v_source_6279_: *mut crate::leanh::LeanObject,
    mut v_target_6280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: u8 = 0;
    let mut v_es_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6281_ = lean_array_get_size(v_source_6279_);
                v___x_6282_ = lean_nat_dec_lt(v_i_6278_, v___x_6281_);
                if v___x_6282_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_6279_);
                    crate::leanh::lean_dec(v_i_6278_);
                    return v_target_6280_;
                } else {
                    v_es_6283_ = lean_array_fget(v_source_6279_, v_i_6278_);
                    v___x_6284_ = crate::leanh::lean_box(0);
                    v_source_6285_ = lean_array_fset(v_source_6279_, v_i_6278_, v___x_6284_);
                    v_target_6286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_target_6280_, v_es_6283_);
                    v___x_6287_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6288_ = lean_nat_add(v_i_6278_, v___x_6287_);
                    crate::leanh::lean_dec(v_i_6278_);
                    v_i_6278_ = v___x_6288_;
                    v_source_6279_ = v_source_6285_;
                    v_target_6280_ = v_target_6286_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(
    mut v_data_6290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6291_ = lean_array_get_size(v_data_6290_);
    v___x_6292_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6293_ = lean_nat_mul(v___x_6291_, v___x_6292_);
    v___x_6294_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6295_ = crate::leanh::lean_box(0);
    v___x_6296_ = lean_mk_array(v_nbuckets_6293_, v___x_6295_);
    v___x_6297_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v___x_6294_, v_data_6290_, v___x_6296_);
    return v___x_6297_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(
    mut v_m_6298_: *mut crate::leanh::LeanObject,
    mut v_a_6299_: *mut crate::leanh::LeanObject,
    mut v_b_6300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6305_: u8 = 0;
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: u64 = 0;
    let mut v___x_6308_: u64 = 0;
    let mut v___x_6309_: u64 = 0;
    let mut v_fold_6310_: u64 = 0;
    let mut v___x_6311_: u64 = 0;
    let mut v___x_6312_: u64 = 0;
    let mut v___x_6313_: u64 = 0;
    let mut v___x_6314_: usize = 0;
    let mut v___x_6315_: usize = 0;
    let mut v___x_6316_: usize = 0;
    let mut v___x_6317_: usize = 0;
    let mut v___x_6318_: usize = 0;
    let mut v_bkt_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: u8 = 0;
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: u8 = 0;
    let mut v_val_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6301_ = crate::leanh::lean_ctor_get(v_m_6298_, 0);
                v_buckets_6302_ = crate::leanh::lean_ctor_get(v_m_6298_, 1);
                v_isSharedCheck_6345_ = (!crate::leanh::lean_is_exclusive(v_m_6298_)) as u8;
                if v_isSharedCheck_6345_ == 0 {
                    v___x_6304_ = v_m_6298_;
                    v_isShared_6305_ = v_isSharedCheck_6345_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_6302_);
                    crate::leanh::lean_inc(v_size_6301_);
                    crate::leanh::lean_dec(v_m_6298_);
                    v___x_6304_ = crate::leanh::lean_box(0);
                    v_isShared_6305_ = v_isSharedCheck_6345_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6306_ = lean_array_get_size(v_buckets_6302_);
                v___x_6307_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_6299_);
                v___x_6308_ = 32u64;
                v___x_6309_ = lean_uint64_shift_right(v___x_6307_, v___x_6308_);
                v_fold_6310_ = lean_uint64_xor(v___x_6307_, v___x_6309_);
                v___x_6311_ = 16u64;
                v___x_6312_ = lean_uint64_shift_right(v_fold_6310_, v___x_6311_);
                v___x_6313_ = lean_uint64_xor(v_fold_6310_, v___x_6312_);
                v___x_6314_ = lean_uint64_to_usize(v___x_6313_);
                v___x_6315_ = lean_usize_of_nat(v___x_6306_);
                v___x_6316_ = 1usize;
                v___x_6317_ = lean_usize_sub(v___x_6315_, v___x_6316_);
                v___x_6318_ = lean_usize_land(v___x_6314_, v___x_6317_);
                v_bkt_6319_ = lean_array_uget_borrowed(v_buckets_6302_, v___x_6318_);
                v___x_6320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_6299_, v_bkt_6319_);
                if v___x_6320_ == 0 {
                    v___x_6321_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_6322_ = lean_nat_add(v_size_6301_, v___x_6321_);
                    crate::leanh::lean_dec(v_size_6301_);
                    crate::leanh::lean_inc(v_bkt_6319_);
                    v___x_6323_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6323_, 0, v_a_6299_);
                    crate::leanh::lean_ctor_set(v___x_6323_, 1, v_b_6300_);
                    crate::leanh::lean_ctor_set(v___x_6323_, 2, v_bkt_6319_);
                    v_buckets_x27_6324_ =
                        lean_array_uset(v_buckets_6302_, v___x_6318_, v___x_6323_);
                    v___x_6325_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_6326_ = lean_nat_mul(v_size_x27_6322_, v___x_6325_);
                    v___x_6327_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6328_ = lean_nat_div(v___x_6326_, v___x_6327_);
                    crate::leanh::lean_dec(v___x_6326_);
                    v___x_6329_ = lean_array_get_size(v_buckets_x27_6324_);
                    v___x_6330_ = lean_nat_dec_le(v___x_6328_, v___x_6329_);
                    crate::leanh::lean_dec(v___x_6328_);
                    if v___x_6330_ == 0 {
                        v_val_6331_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_buckets_x27_6324_);
                        if v_isShared_6305_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6304_, 1, v_val_6331_);
                            crate::leanh::lean_ctor_set(v___x_6304_, 0, v_size_x27_6322_);
                            v___x_6333_ = v___x_6304_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6334_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6334_,
                                0,
                                v_size_x27_6322_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6334_, 1, v_val_6331_);
                            v___x_6333_ = v_reuseFailAlloc_6334_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_6305_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6304_, 1, v_buckets_x27_6324_);
                            crate::leanh::lean_ctor_set(v___x_6304_, 0, v_size_x27_6322_);
                            v___x_6336_ = v___x_6304_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6337_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6337_,
                                0,
                                v_size_x27_6322_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6337_,
                                1,
                                v_buckets_x27_6324_,
                            );
                            v___x_6336_ = v_reuseFailAlloc_6337_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_6319_);
                    v___x_6338_ = crate::leanh::lean_box(0);
                    v_buckets_x27_6339_ =
                        lean_array_uset(v_buckets_6302_, v___x_6318_, v___x_6338_);
                    v___x_6340_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_6299_, v_b_6300_, v_bkt_6319_);
                    v___x_6341_ = lean_array_uset(v_buckets_x27_6339_, v___x_6318_, v___x_6340_);
                    if v_isShared_6305_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6304_, 1, v___x_6341_);
                        v___x_6343_ = v___x_6304_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6344_, 0, v_size_6301_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6344_, 1, v___x_6341_);
                        v___x_6343_ = v_reuseFailAlloc_6344_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6333_;
            }
            3 => {
                return v___x_6336_;
            }
            4 => {
                return v___x_6343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(
    mut v_as_6346_: *mut crate::leanh::LeanObject,
    mut v_i_6347_: usize,
    mut v_stop_6348_: usize,
    mut v_b_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6350_: u8 = 0;
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: usize = 0;
    let mut v___x_6353_: usize = 0;
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6350_ = lean_usize_dec_eq(v_i_6347_, v_stop_6348_);
                if v___x_6350_ == 0 {
                    v___x_6351_ = crate::leanh::lean_box(0);
                    v___x_6352_ = 1usize;
                    v___x_6353_ = lean_usize_sub(v_i_6347_, v___x_6352_);
                    v___x_6354_ = lean_array_uget_borrowed(v_as_6346_, v___x_6353_);
                    v___x_6355_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v___x_6354_);
                    v___x_6356_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_b_6349_, v___x_6355_, v___x_6351_);
                    v_i_6347_ = v___x_6353_;
                    v_b_6349_ = v___x_6356_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6349_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___boxed(
    mut v_as_6358_: *mut crate::leanh::LeanObject,
    mut v_i_6359_: *mut crate::leanh::LeanObject,
    mut v_stop_6360_: *mut crate::leanh::LeanObject,
    mut v_b_6361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6362_: usize = 0;
    let mut v_stop_boxed_6363_: usize = 0;
    let mut v_res_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6362_ = crate::leanh::lean_unbox_usize(v_i_6359_);
    crate::leanh::lean_dec(v_i_6359_);
    v_stop_boxed_6363_ = crate::leanh::lean_unbox_usize(v_stop_6360_);
    crate::leanh::lean_dec(v_stop_6360_);
    v_res_6364_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_as_6358_, v_i_boxed_6362_, v_stop_boxed_6363_, v_b_6361_);
    crate::leanh::lean_dec_ref(v_as_6358_);
    return v_res_6364_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(
    mut v_cs_6365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_alts_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: u8 = 0;
    v_alts_6366_ = crate::leanh::lean_ctor_get(v_cs_6365_, 3);
    v___x_6367_ = lean_array_get_size(v_alts_6366_);
    v___x_6368_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_6369_ = lean_nat_add(v___x_6367_, v___x_6368_);
    v___x_6370_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6371_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_6372_ = lean_nat_mul(v___x_6369_, v___x_6371_);
    crate::leanh::lean_dec(v___x_6369_);
    v___x_6373_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_6374_ = lean_nat_div(v___x_6372_, v___x_6373_);
    crate::leanh::lean_dec(v___x_6372_);
    v___x_6375_ = l_Nat_nextPowerOfTwo(v___x_6374_);
    crate::leanh::lean_dec(v___x_6374_);
    v___x_6376_ = crate::leanh::lean_box(0);
    v___x_6377_ = lean_mk_array(v___x_6375_, v___x_6376_);
    v___x_6378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6378_, 0, v___x_6370_);
    crate::leanh::lean_ctor_set(v___x_6378_, 1, v___x_6377_);
    v___x_6379_ = crate::leanh::lean_box(2);
    v___x_6380_ = crate::leanh::lean_box(0);
    v_map_6381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v___x_6378_, v___x_6379_, v___x_6380_);
    v___x_6382_ = lean_nat_dec_lt(v___x_6370_, v___x_6367_);
    if v___x_6382_ == 0 {
        return v_map_6381_;
    } else {
        let mut v___x_6383_: usize = 0;
        let mut v___x_6384_: usize = 0;
        let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6383_ = lean_usize_of_nat(v___x_6367_);
        v___x_6384_ = 0usize;
        v___x_6385_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(v_alts_6366_, v___x_6383_, v___x_6384_, v_map_6381_);
        return v___x_6385_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(
    mut v_cs_6386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6387_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cs_6386_);
    crate::leanh::lean_dec_ref(v_cs_6386_);
    return v_res_6387_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(
    mut v_00_u03b2_6388_: *mut crate::leanh::LeanObject,
    mut v_m_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_b_6391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6392_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_m_6389_, v_a_6390_, v_b_6391_);
    return v___x_6392_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(
    mut v_00_u03b2_6393_: *mut crate::leanh::LeanObject,
    mut v_a_6394_: *mut crate::leanh::LeanObject,
    mut v_x_6395_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6396_: u8 = 0;
    v___x_6396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___redArg(v_a_6394_, v_x_6395_);
    return v___x_6396_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0___boxed(
    mut v_00_u03b2_6397_: *mut crate::leanh::LeanObject,
    mut v_a_6398_: *mut crate::leanh::LeanObject,
    mut v_x_6399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6400_: u8 = 0;
    let mut v_r_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6400_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__0(v_00_u03b2_6397_, v_a_6398_, v_x_6399_);
    crate::leanh::lean_dec(v_x_6399_);
    crate::leanh::lean_dec(v_a_6398_);
    v_r_6401_ = crate::leanh::lean_box((v_res_6400_) as usize);
    return v_r_6401_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1(
    mut v_00_u03b2_6402_: *mut crate::leanh::LeanObject,
    mut v_data_6403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6404_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1___redArg(v_data_6403_);
    return v___x_6404_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2(
    mut v_00_u03b2_6405_: *mut crate::leanh::LeanObject,
    mut v_a_6406_: *mut crate::leanh::LeanObject,
    mut v_b_6407_: *mut crate::leanh::LeanObject,
    mut v_x_6408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6409_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__2___redArg(v_a_6406_, v_b_6407_, v_x_6408_);
    return v___x_6409_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2(
    mut v_00_u03b2_6410_: *mut crate::leanh::LeanObject,
    mut v_i_6411_: *mut crate::leanh::LeanObject,
    mut v_source_6412_: *mut crate::leanh::LeanObject,
    mut v_target_6413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6414_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2___redArg(v_i_6411_, v_source_6412_, v_target_6413_);
    return v___x_6414_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_6415_: *mut crate::leanh::LeanObject,
    mut v_x_6416_: *mut crate::leanh::LeanObject,
    mut v_x_6417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6418_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0_spec__1_spec__2_spec__4___redArg(v_x_6416_, v_x_6417_);
    return v___x_6418_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(
    mut v_fvar_6419_: *mut crate::leanh::LeanObject,
    mut v_a_6420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: u8 = 0;
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArms_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6432_: u8 = 0;
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6422_ = lean_st_ref_get(v_a_6420_);
                v_decision_6423_ = crate::leanh::lean_ctor_get(v___x_6422_, 0);
                crate::leanh::lean_inc_ref(v_decision_6423_);
                crate::leanh::lean_dec(v___x_6422_);
                v___x_6424_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_visitArg_spec__0___redArg(v_decision_6423_, v_fvar_6419_);
                crate::leanh::lean_dec_ref(v_decision_6423_);
                if v___x_6424_ == 0 {
                    crate::leanh::lean_dec(v_fvar_6419_);
                    v___x_6425_ = crate::leanh::lean_box(0);
                    v___x_6426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6426_, 0, v___x_6425_);
                    return v___x_6426_;
                } else {
                    v___x_6427_ = lean_st_ref_take(v_a_6420_);
                    v_decision_6428_ = crate::leanh::lean_ctor_get(v___x_6427_, 0);
                    v_newArms_6429_ = crate::leanh::lean_ctor_get(v___x_6427_, 1);
                    v_isSharedCheck_6441_ = (!crate::leanh::lean_is_exclusive(v___x_6427_)) as u8;
                    if v_isSharedCheck_6441_ == 0 {
                        v___x_6431_ = v___x_6427_;
                        v_isShared_6432_ = v_isSharedCheck_6441_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_newArms_6429_);
                        crate::leanh::lean_inc(v_decision_6428_);
                        crate::leanh::lean_dec(v___x_6427_);
                        v___x_6431_ = crate::leanh::lean_box(0);
                        v_isShared_6432_ = v_isSharedCheck_6441_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6433_ = crate::leanh::lean_box(2);
                v___x_6434_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_6428_, v_fvar_6419_, v___x_6433_);
                if v_isShared_6432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6431_, 0, v___x_6434_);
                    v___x_6436_ = v___x_6431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6440_, 0, v___x_6434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6440_, 1, v_newArms_6429_);
                    v___x_6436_ = v_reuseFailAlloc_6440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6437_ = lean_st_ref_set(v_a_6420_, v___x_6436_);
                v___x_6438_ = crate::leanh::lean_box(0);
                v___x_6439_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6439_, 0, v___x_6438_);
                return v___x_6439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(
    mut v_fvar_6442_: *mut crate::leanh::LeanObject,
    mut v_a_6443_: *mut crate::leanh::LeanObject,
    mut v_a_6444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6445_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_6442_, v_a_6443_);
    crate::leanh::lean_dec(v_a_6443_);
    return v_res_6445_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(
    mut v_fvar_6446_: *mut crate::leanh::LeanObject,
    mut v_a_6447_: *mut crate::leanh::LeanObject,
    mut v_a_6448_: *mut crate::leanh::LeanObject,
    mut v_a_6449_: *mut crate::leanh::LeanObject,
    mut v_a_6450_: *mut crate::leanh::LeanObject,
    mut v_a_6451_: *mut crate::leanh::LeanObject,
    mut v_a_6452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6454_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvar_6446_, v_a_6447_);
    return v___x_6454_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(
    mut v_fvar_6455_: *mut crate::leanh::LeanObject,
    mut v_a_6456_: *mut crate::leanh::LeanObject,
    mut v_a_6457_: *mut crate::leanh::LeanObject,
    mut v_a_6458_: *mut crate::leanh::LeanObject,
    mut v_a_6459_: *mut crate::leanh::LeanObject,
    mut v_a_6460_: *mut crate::leanh::LeanObject,
    mut v_a_6461_: *mut crate::leanh::LeanObject,
    mut v_a_6462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6463_ =
        l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(
            v_fvar_6455_,
            v_a_6456_,
            v_a_6457_,
            v_a_6458_,
            v_a_6459_,
            v_a_6460_,
            v_a_6461_,
        );
    crate::leanh::lean_dec(v_a_6461_);
    crate::leanh::lean_dec_ref(v_a_6460_);
    crate::leanh::lean_dec(v_a_6459_);
    crate::leanh::lean_dec_ref(v_a_6458_);
    crate::leanh::lean_dec(v_a_6457_);
    crate::leanh::lean_dec(v_a_6456_);
    return v_res_6463_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(
    mut v_msg_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
    mut v___y_6468_: *mut crate::leanh::LeanObject,
    mut v___y_6469_: *mut crate::leanh::LeanObject,
    mut v___y_6470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6477_: u8 = 0;
    let mut v_toFunctor_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6484_: u8 = 0;
    let mut v___f_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6501_: u8 = 0;
    let mut v_toFunctor_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6508_: u8 = 0;
    let mut v___f_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12636__overap_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6529_: u8 = 0;
    let mut v_unused_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6531_: u8 = 0;
    let mut v_unused_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6535_: u8 = 0;
    let mut v_unused_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6537_: u8 = 0;
    let mut v_unused_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__0);
                v___x_6473_ = l_StateRefT_x27_instMonad___redArg(v___x_6472_);
                v_toApplicative_6474_ = crate::leanh::lean_ctor_get(v___x_6473_, 0);
                v_isSharedCheck_6537_ = (!crate::leanh::lean_is_exclusive(v___x_6473_)) as u8;
                if v_isSharedCheck_6537_ == 0 {
                    v_unused_6538_ = crate::leanh::lean_ctor_get(v___x_6473_, 1);
                    crate::leanh::lean_dec(v_unused_6538_);
                    v___x_6476_ = v___x_6473_;
                    v_isShared_6477_ = v_isSharedCheck_6537_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_6474_);
                    crate::leanh::lean_dec(v___x_6473_);
                    v___x_6476_ = crate::leanh::lean_box(0);
                    v_isShared_6477_ = v_isSharedCheck_6537_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_6478_ = crate::leanh::lean_ctor_get(v_toApplicative_6474_, 0);
                v_toSeq_6479_ = crate::leanh::lean_ctor_get(v_toApplicative_6474_, 2);
                v_toSeqLeft_6480_ = crate::leanh::lean_ctor_get(v_toApplicative_6474_, 3);
                v_toSeqRight_6481_ = crate::leanh::lean_ctor_get(v_toApplicative_6474_, 4);
                v_isSharedCheck_6535_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_6474_)) as u8;
                if v_isSharedCheck_6535_ == 0 {
                    v_unused_6536_ = crate::leanh::lean_ctor_get(v_toApplicative_6474_, 1);
                    crate::leanh::lean_dec(v_unused_6536_);
                    v___x_6483_ = v_toApplicative_6474_;
                    v_isShared_6484_ = v_isSharedCheck_6535_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_6481_);
                    crate::leanh::lean_inc(v_toSeqLeft_6480_);
                    crate::leanh::lean_inc(v_toSeq_6479_);
                    crate::leanh::lean_inc(v_toFunctor_6478_);
                    crate::leanh::lean_dec(v_toApplicative_6474_);
                    v___x_6483_ = crate::leanh::lean_box(0);
                    v_isShared_6484_ = v_isSharedCheck_6535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_6485_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__1;
                v___f_6486_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_6478_);
                v___f_6487_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6487_, 0, v_toFunctor_6478_);
                v___f_6488_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6488_, 0, v_toFunctor_6478_);
                v___x_6489_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6489_, 0, v___f_6487_);
                crate::leanh::lean_ctor_set(v___x_6489_, 1, v___f_6488_);
                v___f_6490_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6490_, 0, v_toSeqRight_6481_);
                v___f_6491_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6491_, 0, v_toSeqLeft_6480_);
                v___f_6492_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6492_, 0, v_toSeq_6479_);
                if v_isShared_6484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6483_, 4, v___f_6490_);
                    crate::leanh::lean_ctor_set(v___x_6483_, 3, v___f_6491_);
                    crate::leanh::lean_ctor_set(v___x_6483_, 2, v___f_6492_);
                    crate::leanh::lean_ctor_set(v___x_6483_, 1, v___f_6485_);
                    crate::leanh::lean_ctor_set(v___x_6483_, 0, v___x_6489_);
                    v___x_6494_ = v___x_6483_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6534_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6534_, 0, v___x_6489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6534_, 1, v___f_6485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6534_, 2, v___f_6492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6534_, 3, v___f_6491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6534_, 4, v___f_6490_);
                    v___x_6494_ = v_reuseFailAlloc_6534_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6476_, 1, v___f_6486_);
                    crate::leanh::lean_ctor_set(v___x_6476_, 0, v___x_6494_);
                    v___x_6496_ = v___x_6476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6533_, 0, v___x_6494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6533_, 1, v___f_6486_);
                    v___x_6496_ = v_reuseFailAlloc_6533_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6497_ = l_StateRefT_x27_instMonad___redArg(v___x_6496_);
                v_toApplicative_6498_ = crate::leanh::lean_ctor_get(v___x_6497_, 0);
                v_isSharedCheck_6531_ = (!crate::leanh::lean_is_exclusive(v___x_6497_)) as u8;
                if v_isSharedCheck_6531_ == 0 {
                    v_unused_6532_ = crate::leanh::lean_ctor_get(v___x_6497_, 1);
                    crate::leanh::lean_dec(v_unused_6532_);
                    v___x_6500_ = v___x_6497_;
                    v_isShared_6501_ = v_isSharedCheck_6531_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_6498_);
                    crate::leanh::lean_dec(v___x_6497_);
                    v___x_6500_ = crate::leanh::lean_box(0);
                    v_isShared_6501_ = v_isSharedCheck_6531_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_6502_ = crate::leanh::lean_ctor_get(v_toApplicative_6498_, 0);
                v_toSeq_6503_ = crate::leanh::lean_ctor_get(v_toApplicative_6498_, 2);
                v_toSeqLeft_6504_ = crate::leanh::lean_ctor_get(v_toApplicative_6498_, 3);
                v_toSeqRight_6505_ = crate::leanh::lean_ctor_get(v_toApplicative_6498_, 4);
                v_isSharedCheck_6529_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_6498_)) as u8;
                if v_isSharedCheck_6529_ == 0 {
                    v_unused_6530_ = crate::leanh::lean_ctor_get(v_toApplicative_6498_, 1);
                    crate::leanh::lean_dec(v_unused_6530_);
                    v___x_6507_ = v_toApplicative_6498_;
                    v_isShared_6508_ = v_isSharedCheck_6529_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_6505_);
                    crate::leanh::lean_inc(v_toSeqLeft_6504_);
                    crate::leanh::lean_inc(v_toSeq_6503_);
                    crate::leanh::lean_inc(v_toFunctor_6502_);
                    crate::leanh::lean_dec(v_toApplicative_6498_);
                    v___x_6507_ = crate::leanh::lean_box(0);
                    v_isShared_6508_ = v_isSharedCheck_6529_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_6509_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__3;
                v___f_6510_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_6502_);
                v___f_6511_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6511_, 0, v_toFunctor_6502_);
                v___f_6512_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6512_, 0, v_toFunctor_6502_);
                v___x_6513_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6513_, 0, v___f_6511_);
                crate::leanh::lean_ctor_set(v___x_6513_, 1, v___f_6512_);
                v___f_6514_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6514_, 0, v_toSeqRight_6505_);
                v___f_6515_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6515_, 0, v_toSeqLeft_6504_);
                v___f_6516_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_6516_, 0, v_toSeq_6503_);
                if v_isShared_6508_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6507_, 4, v___f_6514_);
                    crate::leanh::lean_ctor_set(v___x_6507_, 3, v___f_6515_);
                    crate::leanh::lean_ctor_set(v___x_6507_, 2, v___f_6516_);
                    crate::leanh::lean_ctor_set(v___x_6507_, 1, v___f_6509_);
                    crate::leanh::lean_ctor_set(v___x_6507_, 0, v___x_6513_);
                    v___x_6518_ = v___x_6507_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6528_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 0, v___x_6513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 1, v___f_6509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 2, v___f_6516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 3, v___f_6515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6528_, 4, v___f_6514_);
                    v___x_6518_ = v_reuseFailAlloc_6528_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6500_, 1, v___f_6510_);
                    crate::leanh::lean_ctor_set(v___x_6500_, 0, v___x_6518_);
                    v___x_6520_ = v___x_6500_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v___x_6518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 1, v___f_6510_);
                    v___x_6520_ = v_reuseFailAlloc_6527_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6521_ = l_ReaderT_instMonad___redArg(v___x_6520_);
                v___x_6522_ = l_StateRefT_x27_instMonad___redArg(v___x_6521_);
                v___x_6523_ = crate::leanh::lean_box(0);
                v___x_6524_ = l_instInhabitedOfMonad___redArg(v___x_6522_, v___x_6523_);
                v___x_12636__overap_6525_ = lean_panic_fn_borrowed(v___x_6524_, v_msg_6464_);
                crate::leanh::lean_dec(v___x_6524_);
                crate::leanh::lean_inc(v___y_6470_);
                crate::leanh::lean_inc_ref(v___y_6469_);
                crate::leanh::lean_inc(v___y_6468_);
                crate::leanh::lean_inc_ref(v___y_6467_);
                crate::leanh::lean_inc(v___y_6466_);
                crate::leanh::lean_inc(v___y_6465_);
                v___x_6526_ = crate::leanh::lean_apply_7(
                    v___x_12636__overap_6525_,
                    v___y_6465_,
                    v___y_6466_,
                    v___y_6467_,
                    v___y_6468_,
                    v___y_6469_,
                    v___y_6470_,
                    crate::leanh::lean_box(0),
                );
                return v___x_6526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9___boxed(
    mut v_msg_6539_: *mut crate::leanh::LeanObject,
    mut v___y_6540_: *mut crate::leanh::LeanObject,
    mut v___y_6541_: *mut crate::leanh::LeanObject,
    mut v___y_6542_: *mut crate::leanh::LeanObject,
    mut v___y_6543_: *mut crate::leanh::LeanObject,
    mut v___y_6544_: *mut crate::leanh::LeanObject,
    mut v___y_6545_: *mut crate::leanh::LeanObject,
    mut v___y_6546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6547_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v_msg_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_, v___y_6544_, v___y_6545_);
    crate::leanh::lean_dec(v___y_6545_);
    crate::leanh::lean_dec_ref(v___y_6544_);
    crate::leanh::lean_dec(v___y_6543_);
    crate::leanh::lean_dec_ref(v___y_6542_);
    crate::leanh::lean_dec(v___y_6541_);
    crate::leanh::lean_dec(v___y_6540_);
    return v_res_6547_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(
    mut v_f_6548_: *mut crate::leanh::LeanObject,
    mut v_e_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ty_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: u8 = 0;
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6562_ = l_Lean_Expr_hasFVar(v_e_6549_);
                if v___x_6562_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_6549_);
                    crate::leanh::lean_dec_ref(v_f_6548_);
                    v___x_6563_ = crate::leanh::lean_box(0);
                    v___x_6564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6564_, 0, v___x_6563_);
                    return v___x_6564_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_6549_) {
                        1 => {
                            v_fvarId_6565_ = crate::leanh::lean_ctor_get(v_e_6549_, 0);
                            crate::leanh::lean_inc(v_fvarId_6565_);
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 1);
                            crate::leanh::lean_inc(v___y_6555_);
                            crate::leanh::lean_inc_ref(v___y_6554_);
                            crate::leanh::lean_inc(v___y_6553_);
                            crate::leanh::lean_inc_ref(v___y_6552_);
                            crate::leanh::lean_inc(v___y_6551_);
                            crate::leanh::lean_inc(v___y_6550_);
                            v___x_6566_ = crate::leanh::lean_apply_8(
                                v_f_6548_,
                                v_fvarId_6565_,
                                v___y_6550_,
                                v___y_6551_,
                                v___y_6552_,
                                v___y_6553_,
                                v___y_6554_,
                                v___y_6555_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_6566_;
                        }
                        2 => {
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 1);
                            crate::leanh::lean_dec_ref(v_f_6548_);
                            v___x_6567_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
                            v___x_6568_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_6567_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
                            return v___x_6568_;
                        }
                        5 => {
                            v_fn_6569_ = crate::leanh::lean_ctor_get(v_e_6549_, 0);
                            crate::leanh::lean_inc_ref(v_fn_6569_);
                            v_arg_6570_ = crate::leanh::lean_ctor_get(v_e_6549_, 1);
                            crate::leanh::lean_inc_ref(v_arg_6570_);
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 2);
                            crate::leanh::lean_inc_ref(v_f_6548_);
                            v___x_6571_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6548_, v_fn_6569_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
                            if crate::leanh::lean_obj_tag(v___x_6571_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6571_, 1);
                                v_e_6549_ = v_arg_6570_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_arg_6570_);
                                crate::leanh::lean_dec_ref(v_f_6548_);
                                return v___x_6571_;
                            }
                        }
                        6 => {
                            v_binderType_6573_ = crate::leanh::lean_ctor_get(v_e_6549_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_6573_);
                            v_body_6574_ = crate::leanh::lean_ctor_get(v_e_6549_, 2);
                            crate::leanh::lean_inc_ref(v_body_6574_);
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 3);
                            v_ty_6558_ = v_binderType_6573_;
                            v_body_6559_ = v_body_6574_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_binderType_6575_ = crate::leanh::lean_ctor_get(v_e_6549_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_6575_);
                            v_body_6576_ = crate::leanh::lean_ctor_get(v_e_6549_, 2);
                            crate::leanh::lean_inc_ref(v_body_6576_);
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 3);
                            v_ty_6558_ = v_binderType_6575_;
                            v_body_6559_ = v_body_6576_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 4);
                            crate::leanh::lean_dec_ref(v_f_6548_);
                            v___x_6577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
                            v___x_6578_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_6577_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
                            return v___x_6578_;
                        }
                        11 => {
                            crate::leanh::lean_dec_ref_known(v_e_6549_, 3);
                            crate::leanh::lean_dec_ref(v_f_6548_);
                            v___x_6579_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_Param_forFVarM___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___closed__3);
                            v___x_6580_ = l_panic___at___00Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4_spec__9(v___x_6579_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
                            return v___x_6580_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_6549_);
                            crate::leanh::lean_dec_ref(v_f_6548_);
                            v___x_6581_ = crate::leanh::lean_box(0);
                            v___x_6582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6582_, 0, v___x_6581_);
                            return v___x_6582_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_6548_);
                v___x_6560_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6548_, v_ty_6558_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_);
                if crate::leanh::lean_obj_tag(v___x_6560_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6560_, 1);
                    v_e_6549_ = v_body_6559_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_6559_);
                    crate::leanh::lean_dec_ref(v_f_6548_);
                    return v___x_6560_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4___boxed(
    mut v_f_6583_: *mut crate::leanh::LeanObject,
    mut v_e_6584_: *mut crate::leanh::LeanObject,
    mut v___y_6585_: *mut crate::leanh::LeanObject,
    mut v___y_6586_: *mut crate::leanh::LeanObject,
    mut v___y_6587_: *mut crate::leanh::LeanObject,
    mut v___y_6588_: *mut crate::leanh::LeanObject,
    mut v___y_6589_: *mut crate::leanh::LeanObject,
    mut v___y_6590_: *mut crate::leanh::LeanObject,
    mut v___y_6591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6592_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(
            v_f_6583_,
            v_e_6584_,
            v___y_6585_,
            v___y_6586_,
            v___y_6587_,
            v___y_6588_,
            v___y_6589_,
            v___y_6590_,
        );
    crate::leanh::lean_dec(v___y_6590_);
    crate::leanh::lean_dec_ref(v___y_6589_);
    crate::leanh::lean_dec(v___y_6588_);
    crate::leanh::lean_dec_ref(v___y_6587_);
    crate::leanh::lean_dec(v___y_6586_);
    crate::leanh::lean_dec(v___y_6585_);
    return v_res_6592_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(
    mut v_f_6593_: *mut crate::leanh::LeanObject,
    mut v_arg_6594_: *mut crate::leanh::LeanObject,
    mut v___y_6595_: *mut crate::leanh::LeanObject,
    mut v___y_6596_: *mut crate::leanh::LeanObject,
    mut v___y_6597_: *mut crate::leanh::LeanObject,
    mut v___y_6598_: *mut crate::leanh::LeanObject,
    mut v___y_6599_: *mut crate::leanh::LeanObject,
    mut v___y_6600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_arg_6594_) {
        0 => {
            let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_f_6593_);
            v___x_6602_ = crate::leanh::lean_box(0);
            v___x_6603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6603_, 0, v___x_6602_);
            return v___x_6603_;
        }
        1 => {
            let mut v_fvarId_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_6604_ = crate::leanh::lean_ctor_get(v_arg_6594_, 0);
            crate::leanh::lean_inc(v_fvarId_6604_);
            crate::leanh::lean_dec_ref_known(v_arg_6594_, 1);
            crate::leanh::lean_inc(v___y_6600_);
            crate::leanh::lean_inc_ref(v___y_6599_);
            crate::leanh::lean_inc(v___y_6598_);
            crate::leanh::lean_inc_ref(v___y_6597_);
            crate::leanh::lean_inc(v___y_6596_);
            crate::leanh::lean_inc(v___y_6595_);
            v___x_6605_ = crate::leanh::lean_apply_8(
                v_f_6593_,
                v_fvarId_6604_,
                v___y_6595_,
                v___y_6596_,
                v___y_6597_,
                v___y_6598_,
                v___y_6599_,
                v___y_6600_,
                crate::leanh::lean_box(0),
            );
            return v___x_6605_;
        }
        _ => {
            let mut v_expr_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_expr_6606_ = crate::leanh::lean_ctor_get(v_arg_6594_, 0);
            crate::leanh::lean_inc_ref(v_expr_6606_);
            crate::leanh::lean_dec_ref_known(v_arg_6594_, 1);
            v___x_6607_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6593_, v_expr_6606_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_, v___y_6600_);
            return v___x_6607_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg___boxed(
    mut v_f_6608_: *mut crate::leanh::LeanObject,
    mut v_arg_6609_: *mut crate::leanh::LeanObject,
    mut v___y_6610_: *mut crate::leanh::LeanObject,
    mut v___y_6611_: *mut crate::leanh::LeanObject,
    mut v___y_6612_: *mut crate::leanh::LeanObject,
    mut v___y_6613_: *mut crate::leanh::LeanObject,
    mut v___y_6614_: *mut crate::leanh::LeanObject,
    mut v___y_6615_: *mut crate::leanh::LeanObject,
    mut v___y_6616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6617_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_6608_, v_arg_6609_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_);
    crate::leanh::lean_dec(v___y_6615_);
    crate::leanh::lean_dec_ref(v___y_6614_);
    crate::leanh::lean_dec(v___y_6613_);
    crate::leanh::lean_dec_ref(v___y_6612_);
    crate::leanh::lean_dec(v___y_6611_);
    crate::leanh::lean_dec(v___y_6610_);
    return v_res_6617_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(
    mut v_f_6618_: *mut crate::leanh::LeanObject,
    mut v_param_6619_: *mut crate::leanh::LeanObject,
    mut v___y_6620_: *mut crate::leanh::LeanObject,
    mut v___y_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
    mut v___y_6624_: *mut crate::leanh::LeanObject,
    mut v___y_6625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_6627_ = crate::leanh::lean_ctor_get(v_param_6619_, 2);
    crate::leanh::lean_inc_ref(v_type_6627_);
    crate::leanh::lean_dec_ref(v_param_6619_);
    v___x_6628_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(
            v_f_6618_,
            v_type_6627_,
            v___y_6620_,
            v___y_6621_,
            v___y_6622_,
            v___y_6623_,
            v___y_6624_,
            v___y_6625_,
        );
    return v___x_6628_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg___boxed(
    mut v_f_6629_: *mut crate::leanh::LeanObject,
    mut v_param_6630_: *mut crate::leanh::LeanObject,
    mut v___y_6631_: *mut crate::leanh::LeanObject,
    mut v___y_6632_: *mut crate::leanh::LeanObject,
    mut v___y_6633_: *mut crate::leanh::LeanObject,
    mut v___y_6634_: *mut crate::leanh::LeanObject,
    mut v___y_6635_: *mut crate::leanh::LeanObject,
    mut v___y_6636_: *mut crate::leanh::LeanObject,
    mut v___y_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6638_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_6629_, v_param_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_);
    crate::leanh::lean_dec(v___y_6636_);
    crate::leanh::lean_dec_ref(v___y_6635_);
    crate::leanh::lean_dec(v___y_6634_);
    crate::leanh::lean_dec_ref(v___y_6633_);
    crate::leanh::lean_dec(v___y_6632_);
    crate::leanh::lean_dec(v___y_6631_);
    return v_res_6638_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(
    mut v_pu_6639_: u8,
    mut v_f_6640_: *mut crate::leanh::LeanObject,
    mut v_as_6641_: *mut crate::leanh::LeanObject,
    mut v_i_6642_: usize,
    mut v_stop_6643_: usize,
    mut v_b_6644_: *mut crate::leanh::LeanObject,
    mut v___y_6645_: *mut crate::leanh::LeanObject,
    mut v___y_6646_: *mut crate::leanh::LeanObject,
    mut v___y_6647_: *mut crate::leanh::LeanObject,
    mut v___y_6648_: *mut crate::leanh::LeanObject,
    mut v___y_6649_: *mut crate::leanh::LeanObject,
    mut v___y_6650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6652_: u8 = 0;
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: usize = 0;
    let mut v___x_6657_: usize = 0;
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6652_ = lean_usize_dec_eq(v_i_6642_, v_stop_6643_);
                if v___x_6652_ == 0 {
                    v___x_6653_ = lean_array_uget_borrowed(v_as_6641_, v_i_6642_);
                    crate::leanh::lean_inc(v___x_6653_);
                    crate::leanh::lean_inc_ref(v_f_6640_);
                    v___x_6654_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_6640_, v___x_6653_, v___y_6645_, v___y_6646_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
                    if crate::leanh::lean_obj_tag(v___x_6654_) == 0 {
                        v_a_6655_ = crate::leanh::lean_ctor_get(v___x_6654_, 0);
                        crate::leanh::lean_inc(v_a_6655_);
                        crate::leanh::lean_dec_ref_known(v___x_6654_, 1);
                        v___x_6656_ = 1usize;
                        v___x_6657_ = lean_usize_add(v_i_6642_, v___x_6656_);
                        v_i_6642_ = v___x_6657_;
                        v_b_6644_ = v_a_6655_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_6640_);
                        return v___x_6654_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6640_);
                    v___x_6659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6659_, 0, v_b_6644_);
                    return v___x_6659_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6___boxed(
    mut v_pu_6660_: *mut crate::leanh::LeanObject,
    mut v_f_6661_: *mut crate::leanh::LeanObject,
    mut v_as_6662_: *mut crate::leanh::LeanObject,
    mut v_i_6663_: *mut crate::leanh::LeanObject,
    mut v_stop_6664_: *mut crate::leanh::LeanObject,
    mut v_b_6665_: *mut crate::leanh::LeanObject,
    mut v___y_6666_: *mut crate::leanh::LeanObject,
    mut v___y_6667_: *mut crate::leanh::LeanObject,
    mut v___y_6668_: *mut crate::leanh::LeanObject,
    mut v___y_6669_: *mut crate::leanh::LeanObject,
    mut v___y_6670_: *mut crate::leanh::LeanObject,
    mut v___y_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6673_: u8 = 0;
    let mut v_i_boxed_6674_: usize = 0;
    let mut v_stop_boxed_6675_: usize = 0;
    let mut v_res_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6673_ = (crate::leanh::lean_unbox(v_pu_6660_) as u8);
    v_i_boxed_6674_ = crate::leanh::lean_unbox_usize(v_i_6663_);
    crate::leanh::lean_dec(v_i_6663_);
    v_stop_boxed_6675_ = crate::leanh::lean_unbox_usize(v_stop_6664_);
    crate::leanh::lean_dec(v_stop_6664_);
    v_res_6676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_boxed_6673_, v_f_6661_, v_as_6662_, v_i_boxed_6674_, v_stop_boxed_6675_, v_b_6665_, v___y_6666_, v___y_6667_, v___y_6668_, v___y_6669_, v___y_6670_, v___y_6671_);
    crate::leanh::lean_dec(v___y_6671_);
    crate::leanh::lean_dec_ref(v___y_6670_);
    crate::leanh::lean_dec(v___y_6669_);
    crate::leanh::lean_dec_ref(v___y_6668_);
    crate::leanh::lean_dec(v___y_6667_);
    crate::leanh::lean_dec(v___y_6666_);
    crate::leanh::lean_dec_ref(v_as_6662_);
    return v_res_6676_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(
    mut v_pu_6677_: u8,
    mut v_f_6678_: *mut crate::leanh::LeanObject,
    mut v_as_6679_: *mut crate::leanh::LeanObject,
    mut v_i_6680_: usize,
    mut v_stop_6681_: usize,
    mut v_b_6682_: *mut crate::leanh::LeanObject,
    mut v___y_6683_: *mut crate::leanh::LeanObject,
    mut v___y_6684_: *mut crate::leanh::LeanObject,
    mut v___y_6685_: *mut crate::leanh::LeanObject,
    mut v___y_6686_: *mut crate::leanh::LeanObject,
    mut v___y_6687_: *mut crate::leanh::LeanObject,
    mut v___y_6688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6690_: u8 = 0;
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: usize = 0;
    let mut v___x_6695_: usize = 0;
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6690_ = lean_usize_dec_eq(v_i_6680_, v_stop_6681_);
                if v___x_6690_ == 0 {
                    v___x_6691_ = lean_array_uget_borrowed(v_as_6679_, v_i_6680_);
                    crate::leanh::lean_inc(v___x_6691_);
                    crate::leanh::lean_inc_ref(v_f_6678_);
                    v___x_6692_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_6678_, v___x_6691_, v___y_6683_, v___y_6684_, v___y_6685_, v___y_6686_, v___y_6687_, v___y_6688_);
                    if crate::leanh::lean_obj_tag(v___x_6692_) == 0 {
                        v_a_6693_ = crate::leanh::lean_ctor_get(v___x_6692_, 0);
                        crate::leanh::lean_inc(v_a_6693_);
                        crate::leanh::lean_dec_ref_known(v___x_6692_, 1);
                        v___x_6694_ = 1usize;
                        v___x_6695_ = lean_usize_add(v_i_6680_, v___x_6694_);
                        v_i_6680_ = v___x_6695_;
                        v_b_6682_ = v_a_6693_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_6678_);
                        return v___x_6692_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6678_);
                    v___x_6697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6697_, 0, v_b_6682_);
                    return v___x_6697_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4___boxed(
    mut v_pu_6698_: *mut crate::leanh::LeanObject,
    mut v_f_6699_: *mut crate::leanh::LeanObject,
    mut v_as_6700_: *mut crate::leanh::LeanObject,
    mut v_i_6701_: *mut crate::leanh::LeanObject,
    mut v_stop_6702_: *mut crate::leanh::LeanObject,
    mut v_b_6703_: *mut crate::leanh::LeanObject,
    mut v___y_6704_: *mut crate::leanh::LeanObject,
    mut v___y_6705_: *mut crate::leanh::LeanObject,
    mut v___y_6706_: *mut crate::leanh::LeanObject,
    mut v___y_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
    mut v___y_6709_: *mut crate::leanh::LeanObject,
    mut v___y_6710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6711_: u8 = 0;
    let mut v_i_boxed_6712_: usize = 0;
    let mut v_stop_boxed_6713_: usize = 0;
    let mut v_res_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6711_ = (crate::leanh::lean_unbox(v_pu_6698_) as u8);
    v_i_boxed_6712_ = crate::leanh::lean_unbox_usize(v_i_6701_);
    crate::leanh::lean_dec(v_i_6701_);
    v_stop_boxed_6713_ = crate::leanh::lean_unbox_usize(v_stop_6702_);
    crate::leanh::lean_dec(v_stop_6702_);
    v_res_6714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_boxed_6711_, v_f_6699_, v_as_6700_, v_i_boxed_6712_, v_stop_boxed_6713_, v_b_6703_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_);
    crate::leanh::lean_dec(v___y_6709_);
    crate::leanh::lean_dec_ref(v___y_6708_);
    crate::leanh::lean_dec(v___y_6707_);
    crate::leanh::lean_dec_ref(v___y_6706_);
    crate::leanh::lean_dec(v___y_6705_);
    crate::leanh::lean_dec(v___y_6704_);
    crate::leanh::lean_dec_ref(v_as_6700_);
    return v_res_6714_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(
    mut v_pu_6715_: u8,
    mut v_f_6716_: *mut crate::leanh::LeanObject,
    mut v_e_6717_: *mut crate::leanh::LeanObject,
    mut v___y_6718_: *mut crate::leanh::LeanObject,
    mut v___y_6719_: *mut crate::leanh::LeanObject,
    mut v___y_6720_: *mut crate::leanh::LeanObject,
    mut v___y_6721_: *mut crate::leanh::LeanObject,
    mut v___y_6722_: *mut crate::leanh::LeanObject,
    mut v___y_6723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: u8 = 0;
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: u8 = 0;
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: usize = 0;
    let mut v___x_6735_: usize = 0;
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: usize = 0;
    let mut v___x_6738_: usize = 0;
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: u8 = 0;
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: u8 = 0;
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: usize = 0;
    let mut v___x_6751_: usize = 0;
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: usize = 0;
    let mut v___x_6754_: usize = 0;
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: u8 = 0;
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: u8 = 0;
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: usize = 0;
    let mut v___x_6774_: usize = 0;
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: usize = 0;
    let mut v___x_6777_: usize = 0;
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v_unused_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: u8 = 0;
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: u8 = 0;
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: usize = 0;
    let mut v___x_6790_: usize = 0;
    let mut v___x_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: usize = 0;
    let mut v___x_6793_: usize = 0;
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6810_: u8 = 0;
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: u8 = 0;
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: u8 = 0;
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: usize = 0;
    let mut v___x_6823_: usize = 0;
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: usize = 0;
    let mut v___x_6826_: usize = 0;
    let mut v___x_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6828_: u8 = 0;
    let mut v_unused_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_6717_) {
                2 => {
                    v_struct_6740_ = crate::leanh::lean_ctor_get(v_e_6717_, 2);
                    crate::leanh::lean_inc(v_struct_6740_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 3);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6741_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_struct_6740_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6741_;
                }
                3 => {
                    v_args_6742_ = crate::leanh::lean_ctor_get(v_e_6717_, 2);
                    crate::leanh::lean_inc_ref(v_args_6742_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 3);
                    v___x_6743_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6744_ = lean_array_get_size(v_args_6742_);
                    v___x_6745_ = crate::leanh::lean_box(0);
                    v___x_6746_ = lean_nat_dec_lt(v___x_6743_, v___x_6744_);
                    if v___x_6746_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_6742_);
                        crate::leanh::lean_dec_ref(v_f_6716_);
                        v___x_6747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6747_, 0, v___x_6745_);
                        return v___x_6747_;
                    } else {
                        v___x_6748_ = lean_nat_dec_le(v___x_6744_, v___x_6744_);
                        if v___x_6748_ == 0 {
                            if v___x_6746_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_6742_);
                                crate::leanh::lean_dec_ref(v_f_6716_);
                                v___x_6749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6749_, 0, v___x_6745_);
                                return v___x_6749_;
                            } else {
                                v___x_6750_ = 0usize;
                                v___x_6751_ = lean_usize_of_nat(v___x_6744_);
                                v___x_6752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6742_, v___x_6750_, v___x_6751_, v___x_6745_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                                crate::leanh::lean_dec_ref(v_args_6742_);
                                return v___x_6752_;
                            }
                        } else {
                            v___x_6753_ = 0usize;
                            v___x_6754_ = lean_usize_of_nat(v___x_6744_);
                            v___x_6755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6742_, v___x_6753_, v___x_6754_, v___x_6745_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                            crate::leanh::lean_dec_ref(v_args_6742_);
                            return v___x_6755_;
                        }
                    }
                }
                4 => {
                    v_fvarId_6756_ = crate::leanh::lean_ctor_get(v_e_6717_, 0);
                    crate::leanh::lean_inc(v_fvarId_6756_);
                    v_args_6757_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc_ref(v_args_6757_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    crate::leanh::lean_inc_ref(v_f_6716_);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6758_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_fvarId_6756_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6758_) == 0 {
                        v_isSharedCheck_6779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6758_)) as u8;
                        if v_isSharedCheck_6779_ == 0 {
                            v_unused_6780_ = crate::leanh::lean_ctor_get(v___x_6758_, 0);
                            crate::leanh::lean_dec(v_unused_6780_);
                            v___x_6760_ = v___x_6758_;
                            v_isShared_6761_ = v_isSharedCheck_6779_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6758_);
                            v___x_6760_ = crate::leanh::lean_box(0);
                            v_isShared_6761_ = v_isSharedCheck_6779_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_6757_);
                        crate::leanh::lean_dec_ref(v_f_6716_);
                        return v___x_6758_;
                    }
                }
                5 => {
                    v_args_6781_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc_ref(v_args_6781_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    v___x_6782_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6783_ = lean_array_get_size(v_args_6781_);
                    v___x_6784_ = crate::leanh::lean_box(0);
                    v___x_6785_ = lean_nat_dec_lt(v___x_6782_, v___x_6783_);
                    if v___x_6785_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_6781_);
                        crate::leanh::lean_dec_ref(v_f_6716_);
                        v___x_6786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6786_, 0, v___x_6784_);
                        return v___x_6786_;
                    } else {
                        v___x_6787_ = lean_nat_dec_le(v___x_6783_, v___x_6783_);
                        if v___x_6787_ == 0 {
                            if v___x_6785_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_6781_);
                                crate::leanh::lean_dec_ref(v_f_6716_);
                                v___x_6788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6788_, 0, v___x_6784_);
                                return v___x_6788_;
                            } else {
                                v___x_6789_ = 0usize;
                                v___x_6790_ = lean_usize_of_nat(v___x_6783_);
                                v___x_6791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6781_, v___x_6789_, v___x_6790_, v___x_6784_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                                crate::leanh::lean_dec_ref(v_args_6781_);
                                return v___x_6791_;
                            }
                        } else {
                            v___x_6792_ = 0usize;
                            v___x_6793_ = lean_usize_of_nat(v___x_6783_);
                            v___x_6794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6781_, v___x_6792_, v___x_6793_, v___x_6784_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                            crate::leanh::lean_dec_ref(v_args_6781_);
                            return v___x_6794_;
                        }
                    }
                }
                6 => {
                    v_var_6795_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc(v_var_6795_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6796_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_var_6795_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6796_;
                }
                7 => {
                    v_var_6797_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc(v_var_6797_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6798_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_var_6797_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6798_;
                }
                8 => {
                    v_var_6799_ = crate::leanh::lean_ctor_get(v_e_6717_, 2);
                    crate::leanh::lean_inc(v_var_6799_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 3);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6800_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_var_6799_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6800_;
                }
                9 => {
                    v_args_6801_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc_ref(v_args_6801_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    v_args_6726_ = v_args_6801_;
                    state = 1;
                    continue;
                }
                10 => {
                    v_args_6802_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc_ref(v_args_6802_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    v_args_6726_ = v_args_6802_;
                    state = 1;
                    continue;
                }
                11 => {
                    v_var_6803_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc(v_var_6803_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6804_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_var_6803_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6804_;
                }
                12 => {
                    v_var_6805_ = crate::leanh::lean_ctor_get(v_e_6717_, 0);
                    crate::leanh::lean_inc(v_var_6805_);
                    v_args_6806_ = crate::leanh::lean_ctor_get(v_e_6717_, 2);
                    crate::leanh::lean_inc_ref(v_args_6806_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 3);
                    crate::leanh::lean_inc_ref(v_f_6716_);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6807_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_var_6805_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6807_) == 0 {
                        v_isSharedCheck_6828_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6807_)) as u8;
                        if v_isSharedCheck_6828_ == 0 {
                            v_unused_6829_ = crate::leanh::lean_ctor_get(v___x_6807_, 0);
                            crate::leanh::lean_dec(v_unused_6829_);
                            v___x_6809_ = v___x_6807_;
                            v_isShared_6810_ = v_isSharedCheck_6828_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6807_);
                            v___x_6809_ = crate::leanh::lean_box(0);
                            v_isShared_6810_ = v_isSharedCheck_6828_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_6806_);
                        crate::leanh::lean_dec_ref(v_f_6716_);
                        return v___x_6807_;
                    }
                }
                13 => {
                    v_fvarId_6830_ = crate::leanh::lean_ctor_get(v_e_6717_, 1);
                    crate::leanh::lean_inc(v_fvarId_6830_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 2);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6831_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_fvarId_6830_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6831_;
                }
                14 => {
                    v_fvarId_6832_ = crate::leanh::lean_ctor_get(v_e_6717_, 0);
                    crate::leanh::lean_inc(v_fvarId_6832_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 1);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6833_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_fvarId_6832_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6833_;
                }
                15 => {
                    v_fvarId_6834_ = crate::leanh::lean_ctor_get(v_e_6717_, 0);
                    crate::leanh::lean_inc(v_fvarId_6834_);
                    crate::leanh::lean_dec_ref_known(v_e_6717_, 1);
                    crate::leanh::lean_inc(v___y_6723_);
                    crate::leanh::lean_inc_ref(v___y_6722_);
                    crate::leanh::lean_inc(v___y_6721_);
                    crate::leanh::lean_inc_ref(v___y_6720_);
                    crate::leanh::lean_inc(v___y_6719_);
                    crate::leanh::lean_inc(v___y_6718_);
                    v___x_6835_ = crate::leanh::lean_apply_8(
                        v_f_6716_,
                        v_fvarId_6834_,
                        v___y_6718_,
                        v___y_6719_,
                        v___y_6720_,
                        v___y_6721_,
                        v___y_6722_,
                        v___y_6723_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_6835_;
                }
                _ => {
                    crate::leanh::lean_dec(v_e_6717_);
                    crate::leanh::lean_dec_ref(v_f_6716_);
                    v___x_6836_ = crate::leanh::lean_box(0);
                    v___x_6837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6837_, 0, v___x_6836_);
                    return v___x_6837_;
                }
            },
            1 => {
                v___x_6727_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6728_ = lean_array_get_size(v_args_6726_);
                v___x_6729_ = crate::leanh::lean_box(0);
                v___x_6730_ = lean_nat_dec_lt(v___x_6727_, v___x_6728_);
                if v___x_6730_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_6726_);
                    crate::leanh::lean_dec_ref(v_f_6716_);
                    v___x_6731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6731_, 0, v___x_6729_);
                    return v___x_6731_;
                } else {
                    v___x_6732_ = lean_nat_dec_le(v___x_6728_, v___x_6728_);
                    if v___x_6732_ == 0 {
                        if v___x_6730_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_6726_);
                            crate::leanh::lean_dec_ref(v_f_6716_);
                            v___x_6733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6733_, 0, v___x_6729_);
                            return v___x_6733_;
                        } else {
                            v___x_6734_ = 0usize;
                            v___x_6735_ = lean_usize_of_nat(v___x_6728_);
                            v___x_6736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6726_, v___x_6734_, v___x_6735_, v___x_6729_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                            crate::leanh::lean_dec_ref(v_args_6726_);
                            return v___x_6736_;
                        }
                    } else {
                        v___x_6737_ = 0usize;
                        v___x_6738_ = lean_usize_of_nat(v___x_6728_);
                        v___x_6739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6726_, v___x_6737_, v___x_6738_, v___x_6729_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                        crate::leanh::lean_dec_ref(v_args_6726_);
                        return v___x_6739_;
                    }
                }
            }
            2 => {
                v___x_6762_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6763_ = lean_array_get_size(v_args_6757_);
                v___x_6764_ = crate::leanh::lean_box(0);
                v___x_6765_ = lean_nat_dec_lt(v___x_6762_, v___x_6763_);
                if v___x_6765_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_6757_);
                    crate::leanh::lean_dec_ref(v_f_6716_);
                    if v_isShared_6761_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6760_, 0, v___x_6764_);
                        v___x_6767_ = v___x_6760_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6768_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6768_, 0, v___x_6764_);
                        v___x_6767_ = v_reuseFailAlloc_6768_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_6769_ = lean_nat_dec_le(v___x_6763_, v___x_6763_);
                    if v___x_6769_ == 0 {
                        if v___x_6765_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_6757_);
                            crate::leanh::lean_dec_ref(v_f_6716_);
                            if v_isShared_6761_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6760_, 0, v___x_6764_);
                                v___x_6771_ = v___x_6760_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_6772_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6772_, 0, v___x_6764_);
                                v___x_6771_ = v_reuseFailAlloc_6772_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6760_);
                            v___x_6773_ = 0usize;
                            v___x_6774_ = lean_usize_of_nat(v___x_6763_);
                            v___x_6775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6757_, v___x_6773_, v___x_6774_, v___x_6764_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                            crate::leanh::lean_dec_ref(v_args_6757_);
                            return v___x_6775_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6760_);
                        v___x_6776_ = 0usize;
                        v___x_6777_ = lean_usize_of_nat(v___x_6763_);
                        v___x_6778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6757_, v___x_6776_, v___x_6777_, v___x_6764_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                        crate::leanh::lean_dec_ref(v_args_6757_);
                        return v___x_6778_;
                    }
                }
            }
            3 => {
                return v___x_6767_;
            }
            4 => {
                return v___x_6771_;
            }
            5 => {
                v___x_6811_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6812_ = lean_array_get_size(v_args_6806_);
                v___x_6813_ = crate::leanh::lean_box(0);
                v___x_6814_ = lean_nat_dec_lt(v___x_6811_, v___x_6812_);
                if v___x_6814_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_6806_);
                    crate::leanh::lean_dec_ref(v_f_6716_);
                    if v_isShared_6810_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6809_, 0, v___x_6813_);
                        v___x_6816_ = v___x_6809_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6817_, 0, v___x_6813_);
                        v___x_6816_ = v_reuseFailAlloc_6817_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_6818_ = lean_nat_dec_le(v___x_6812_, v___x_6812_);
                    if v___x_6818_ == 0 {
                        if v___x_6814_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_6806_);
                            crate::leanh::lean_dec_ref(v_f_6716_);
                            if v_isShared_6810_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6809_, 0, v___x_6813_);
                                v___x_6820_ = v___x_6809_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_6821_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6821_, 0, v___x_6813_);
                                v___x_6820_ = v_reuseFailAlloc_6821_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6809_);
                            v___x_6822_ = 0usize;
                            v___x_6823_ = lean_usize_of_nat(v___x_6812_);
                            v___x_6824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6806_, v___x_6822_, v___x_6823_, v___x_6813_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                            crate::leanh::lean_dec_ref(v_args_6806_);
                            return v___x_6824_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6809_);
                        v___x_6825_ = 0usize;
                        v___x_6826_ = lean_usize_of_nat(v___x_6812_);
                        v___x_6827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6715_, v_f_6716_, v_args_6806_, v___x_6825_, v___x_6826_, v___x_6813_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
                        crate::leanh::lean_dec_ref(v_args_6806_);
                        return v___x_6827_;
                    }
                }
            }
            6 => {
                return v___x_6816_;
            }
            7 => {
                return v___x_6820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2___boxed(
    mut v_pu_6838_: *mut crate::leanh::LeanObject,
    mut v_f_6839_: *mut crate::leanh::LeanObject,
    mut v_e_6840_: *mut crate::leanh::LeanObject,
    mut v___y_6841_: *mut crate::leanh::LeanObject,
    mut v___y_6842_: *mut crate::leanh::LeanObject,
    mut v___y_6843_: *mut crate::leanh::LeanObject,
    mut v___y_6844_: *mut crate::leanh::LeanObject,
    mut v___y_6845_: *mut crate::leanh::LeanObject,
    mut v___y_6846_: *mut crate::leanh::LeanObject,
    mut v___y_6847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6848_: u8 = 0;
    let mut v_res_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6848_ = (crate::leanh::lean_unbox(v_pu_6838_) as u8);
    v_res_6849_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_boxed_6848_, v_f_6839_, v_e_6840_, v___y_6841_, v___y_6842_, v___y_6843_, v___y_6844_, v___y_6845_, v___y_6846_);
    crate::leanh::lean_dec(v___y_6846_);
    crate::leanh::lean_dec_ref(v___y_6845_);
    crate::leanh::lean_dec(v___y_6844_);
    crate::leanh::lean_dec_ref(v___y_6843_);
    crate::leanh::lean_dec(v___y_6842_);
    crate::leanh::lean_dec(v___y_6841_);
    return v_res_6849_;
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(
    mut v_pu_6850_: u8,
    mut v_f_6851_: *mut crate::leanh::LeanObject,
    mut v_decl_6852_: *mut crate::leanh::LeanObject,
    mut v___y_6853_: *mut crate::leanh::LeanObject,
    mut v___y_6854_: *mut crate::leanh::LeanObject,
    mut v___y_6855_: *mut crate::leanh::LeanObject,
    mut v___y_6856_: *mut crate::leanh::LeanObject,
    mut v___y_6857_: *mut crate::leanh::LeanObject,
    mut v___y_6858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_6860_ = crate::leanh::lean_ctor_get(v_decl_6852_, 2);
    crate::leanh::lean_inc_ref(v_type_6860_);
    v_value_6861_ = crate::leanh::lean_ctor_get(v_decl_6852_, 3);
    crate::leanh::lean_inc(v_value_6861_);
    crate::leanh::lean_dec_ref(v_decl_6852_);
    crate::leanh::lean_inc_ref(v_f_6851_);
    v___x_6862_ =
        l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(
            v_f_6851_,
            v_type_6860_,
            v___y_6853_,
            v___y_6854_,
            v___y_6855_,
            v___y_6856_,
            v___y_6857_,
            v___y_6858_,
        );
    if crate::leanh::lean_obj_tag(v___x_6862_) == 0 {
        let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_6862_, 1);
        v___x_6863_ = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2(v_pu_6850_, v_f_6851_, v_value_6861_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_);
        return v___x_6863_;
    } else {
        crate::leanh::lean_dec(v_value_6861_);
        crate::leanh::lean_dec_ref(v_f_6851_);
        return v___x_6862_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1___boxed(
    mut v_pu_6864_: *mut crate::leanh::LeanObject,
    mut v_f_6865_: *mut crate::leanh::LeanObject,
    mut v_decl_6866_: *mut crate::leanh::LeanObject,
    mut v___y_6867_: *mut crate::leanh::LeanObject,
    mut v___y_6868_: *mut crate::leanh::LeanObject,
    mut v___y_6869_: *mut crate::leanh::LeanObject,
    mut v___y_6870_: *mut crate::leanh::LeanObject,
    mut v___y_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6874_: u8 = 0;
    let mut v_res_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6874_ = (crate::leanh::lean_unbox(v_pu_6864_) as u8);
    v_res_6875_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_boxed_6874_, v_f_6865_, v_decl_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_);
    crate::leanh::lean_dec(v___y_6872_);
    crate::leanh::lean_dec_ref(v___y_6871_);
    crate::leanh::lean_dec(v___y_6870_);
    crate::leanh::lean_dec_ref(v___y_6869_);
    crate::leanh::lean_dec(v___y_6868_);
    crate::leanh::lean_dec(v___y_6867_);
    return v_res_6875_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(
    mut v_alt_6876_: *mut crate::leanh::LeanObject,
    mut v_f_6877_: *mut crate::leanh::LeanObject,
    mut v___y_6878_: *mut crate::leanh::LeanObject,
    mut v___y_6879_: *mut crate::leanh::LeanObject,
    mut v___y_6880_: *mut crate::leanh::LeanObject,
    mut v___y_6881_: *mut crate::leanh::LeanObject,
    mut v___y_6882_: *mut crate::leanh::LeanObject,
    mut v___y_6883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_alt_6876_) {
        0 => {
            let mut v_code_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_6885_ = crate::leanh::lean_ctor_get(v_alt_6876_, 2);
            crate::leanh::lean_inc_ref(v_code_6885_);
            crate::leanh::lean_dec_ref_known(v_alt_6876_, 3);
            crate::leanh::lean_inc(v___y_6883_);
            crate::leanh::lean_inc_ref(v___y_6882_);
            crate::leanh::lean_inc(v___y_6881_);
            crate::leanh::lean_inc_ref(v___y_6880_);
            crate::leanh::lean_inc(v___y_6879_);
            crate::leanh::lean_inc(v___y_6878_);
            v___x_6886_ = crate::leanh::lean_apply_8(
                v_f_6877_,
                v_code_6885_,
                v___y_6878_,
                v___y_6879_,
                v___y_6880_,
                v___y_6881_,
                v___y_6882_,
                v___y_6883_,
                crate::leanh::lean_box(0),
            );
            return v___x_6886_;
        }
        1 => {
            let mut v_code_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_6887_ = crate::leanh::lean_ctor_get(v_alt_6876_, 1);
            crate::leanh::lean_inc_ref(v_code_6887_);
            crate::leanh::lean_dec_ref_known(v_alt_6876_, 2);
            crate::leanh::lean_inc(v___y_6883_);
            crate::leanh::lean_inc_ref(v___y_6882_);
            crate::leanh::lean_inc(v___y_6881_);
            crate::leanh::lean_inc_ref(v___y_6880_);
            crate::leanh::lean_inc(v___y_6879_);
            crate::leanh::lean_inc(v___y_6878_);
            v___x_6888_ = crate::leanh::lean_apply_8(
                v_f_6877_,
                v_code_6887_,
                v___y_6878_,
                v___y_6879_,
                v___y_6880_,
                v___y_6881_,
                v___y_6882_,
                v___y_6883_,
                crate::leanh::lean_box(0),
            );
            return v___x_6888_;
        }
        _ => {
            let mut v_code_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_code_6889_ = crate::leanh::lean_ctor_get(v_alt_6876_, 0);
            crate::leanh::lean_inc_ref(v_code_6889_);
            crate::leanh::lean_dec_ref_known(v_alt_6876_, 1);
            crate::leanh::lean_inc(v___y_6883_);
            crate::leanh::lean_inc_ref(v___y_6882_);
            crate::leanh::lean_inc(v___y_6881_);
            crate::leanh::lean_inc_ref(v___y_6880_);
            crate::leanh::lean_inc(v___y_6879_);
            crate::leanh::lean_inc(v___y_6878_);
            v___x_6890_ = crate::leanh::lean_apply_8(
                v_f_6877_,
                v_code_6889_,
                v___y_6878_,
                v___y_6879_,
                v___y_6880_,
                v___y_6881_,
                v___y_6882_,
                v___y_6883_,
                crate::leanh::lean_box(0),
            );
            return v___x_6890_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_alt_6891_: *mut crate::leanh::LeanObject,
    mut v_f_6892_: *mut crate::leanh::LeanObject,
    mut v___y_6893_: *mut crate::leanh::LeanObject,
    mut v___y_6894_: *mut crate::leanh::LeanObject,
    mut v___y_6895_: *mut crate::leanh::LeanObject,
    mut v___y_6896_: *mut crate::leanh::LeanObject,
    mut v___y_6897_: *mut crate::leanh::LeanObject,
    mut v___y_6898_: *mut crate::leanh::LeanObject,
    mut v___y_6899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6900_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_6891_, v_f_6892_, v___y_6893_, v___y_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
    crate::leanh::lean_dec(v___y_6898_);
    crate::leanh::lean_dec_ref(v___y_6897_);
    crate::leanh::lean_dec(v___y_6896_);
    crate::leanh::lean_dec_ref(v___y_6895_);
    crate::leanh::lean_dec(v___y_6894_);
    crate::leanh::lean_dec(v___y_6893_);
    return v_res_6900_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed(
    mut v_pu_6901_: *mut crate::leanh::LeanObject,
    mut v_f_6902_: *mut crate::leanh::LeanObject,
    mut v___y_6903_: *mut crate::leanh::LeanObject,
    mut v___y_6904_: *mut crate::leanh::LeanObject,
    mut v___y_6905_: *mut crate::leanh::LeanObject,
    mut v___y_6906_: *mut crate::leanh::LeanObject,
    mut v___y_6907_: *mut crate::leanh::LeanObject,
    mut v___y_6908_: *mut crate::leanh::LeanObject,
    mut v___y_6909_: *mut crate::leanh::LeanObject,
    mut v___y_6910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_6911_: u8 = 0;
    let mut v_res_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_6911_ = (crate::leanh::lean_unbox(v_pu_6901_) as u8);
    v_res_6912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(v_pu_boxed_6911_, v_f_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_);
    crate::leanh::lean_dec(v___y_6909_);
    crate::leanh::lean_dec_ref(v___y_6908_);
    crate::leanh::lean_dec(v___y_6907_);
    crate::leanh::lean_dec_ref(v___y_6906_);
    crate::leanh::lean_dec(v___y_6905_);
    crate::leanh::lean_dec(v___y_6904_);
    return v_res_6912_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(
    mut v_pu_6913_: u8,
    mut v_f_6914_: *mut crate::leanh::LeanObject,
    mut v_as_6915_: *mut crate::leanh::LeanObject,
    mut v_i_6916_: usize,
    mut v_stop_6917_: usize,
    mut v_b_6918_: *mut crate::leanh::LeanObject,
    mut v___y_6919_: *mut crate::leanh::LeanObject,
    mut v___y_6920_: *mut crate::leanh::LeanObject,
    mut v___y_6921_: *mut crate::leanh::LeanObject,
    mut v___y_6922_: *mut crate::leanh::LeanObject,
    mut v___y_6923_: *mut crate::leanh::LeanObject,
    mut v___y_6924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6926_: u8 = 0;
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: usize = 0;
    let mut v___x_6933_: usize = 0;
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6926_ = lean_usize_dec_eq(v_i_6916_, v_stop_6917_);
                if v___x_6926_ == 0 {
                    v___x_6927_ = crate::leanh::lean_box((v_pu_6913_) as usize);
                    crate::leanh::lean_inc_ref(v_f_6914_);
                    v___f_6928_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    crate::leanh::lean_closure_set(v___f_6928_, 0, v___x_6927_);
                    crate::leanh::lean_closure_set(v___f_6928_, 1, v_f_6914_);
                    v___x_6929_ = lean_array_uget_borrowed(v_as_6915_, v_i_6916_);
                    crate::leanh::lean_inc(v___x_6929_);
                    v___x_6930_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v___x_6929_, v___f_6928_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_, v___y_6923_, v___y_6924_);
                    if crate::leanh::lean_obj_tag(v___x_6930_) == 0 {
                        v_a_6931_ = crate::leanh::lean_ctor_get(v___x_6930_, 0);
                        crate::leanh::lean_inc(v_a_6931_);
                        crate::leanh::lean_dec_ref_known(v___x_6930_, 1);
                        v___x_6932_ = 1usize;
                        v___x_6933_ = lean_usize_add(v_i_6916_, v___x_6932_);
                        v_i_6916_ = v___x_6933_;
                        v_b_6918_ = v_a_6931_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_6914_);
                        return v___x_6930_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6914_);
                    v___x_6935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6935_, 0, v_b_6918_);
                    return v___x_6935_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(
    mut v_pu_6936_: u8,
    mut v_f_6937_: *mut crate::leanh::LeanObject,
    mut v_c_6938_: *mut crate::leanh::LeanObject,
    mut v___y_6939_: *mut crate::leanh::LeanObject,
    mut v___y_6940_: *mut crate::leanh::LeanObject,
    mut v___y_6941_: *mut crate::leanh::LeanObject,
    mut v___y_6942_: *mut crate::leanh::LeanObject,
    mut v___y_6943_: *mut crate::leanh::LeanObject,
    mut v___y_6944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: u8 = 0;
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: u8 = 0;
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: usize = 0;
    let mut v___x_6968_: usize = 0;
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: usize = 0;
    let mut v___x_6971_: usize = 0;
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6973_: u8 = 0;
    let mut v_unused_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6983_: u8 = 0;
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: u8 = 0;
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: u8 = 0;
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: usize = 0;
    let mut v___x_6996_: usize = 0;
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: usize = 0;
    let mut v___x_6999_: usize = 0;
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7001_: u8 = 0;
    let mut v_unused_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: u8 = 0;
    let mut v___x_7066_: usize = 0;
    let mut v___x_7067_: usize = 0;
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: usize = 0;
    let mut v___x_7070_: usize = 0;
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_6938_) {
                0 => {
                    v_decl_6946_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc_ref(v_decl_6946_);
                    v_k_6947_ = crate::leanh::lean_ctor_get(v_c_6938_, 1);
                    crate::leanh::lean_inc_ref(v_k_6947_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 2);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    v___x_6948_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v_pu_6936_, v_f_6937_, v_decl_6946_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                    if crate::leanh::lean_obj_tag(v___x_6948_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6948_, 1);
                        v_c_6938_ = v_k_6947_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_6947_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_6948_;
                    }
                }
                3 => {
                    v_fvarId_6950_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_6950_);
                    v_args_6951_ = crate::leanh::lean_ctor_get(v_c_6938_, 1);
                    crate::leanh::lean_inc_ref(v_args_6951_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 2);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_6952_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_6950_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6952_) == 0 {
                        v_isSharedCheck_6973_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6952_)) as u8;
                        if v_isSharedCheck_6973_ == 0 {
                            v_unused_6974_ = crate::leanh::lean_ctor_get(v___x_6952_, 0);
                            crate::leanh::lean_dec(v_unused_6974_);
                            v___x_6954_ = v___x_6952_;
                            v_isShared_6955_ = v_isSharedCheck_6973_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6952_);
                            v___x_6954_ = crate::leanh::lean_box(0);
                            v_isShared_6955_ = v_isSharedCheck_6973_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_6951_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_6952_;
                    }
                }
                4 => {
                    v_cases_6975_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc_ref(v_cases_6975_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 1);
                    v_resultType_6976_ = crate::leanh::lean_ctor_get(v_cases_6975_, 1);
                    crate::leanh::lean_inc_ref(v_resultType_6976_);
                    v_discr_6977_ = crate::leanh::lean_ctor_get(v_cases_6975_, 2);
                    crate::leanh::lean_inc(v_discr_6977_);
                    v_alts_6978_ = crate::leanh::lean_ctor_get(v_cases_6975_, 3);
                    crate::leanh::lean_inc_ref(v_alts_6978_);
                    crate::leanh::lean_dec_ref(v_cases_6975_);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    v___x_6979_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6937_, v_resultType_6976_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                    if crate::leanh::lean_obj_tag(v___x_6979_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6979_, 1);
                        crate::leanh::lean_inc_ref(v_f_6937_);
                        crate::leanh::lean_inc(v___y_6944_);
                        crate::leanh::lean_inc_ref(v___y_6943_);
                        crate::leanh::lean_inc(v___y_6942_);
                        crate::leanh::lean_inc_ref(v___y_6941_);
                        crate::leanh::lean_inc(v___y_6940_);
                        crate::leanh::lean_inc(v___y_6939_);
                        v___x_6980_ = crate::leanh::lean_apply_8(
                            v_f_6937_,
                            v_discr_6977_,
                            v___y_6939_,
                            v___y_6940_,
                            v___y_6941_,
                            v___y_6942_,
                            v___y_6943_,
                            v___y_6944_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_6980_) == 0 {
                            v_isSharedCheck_7001_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6980_)) as u8;
                            if v_isSharedCheck_7001_ == 0 {
                                v_unused_7002_ = crate::leanh::lean_ctor_get(v___x_6980_, 0);
                                crate::leanh::lean_dec(v_unused_7002_);
                                v___x_6982_ = v___x_6980_;
                                v_isShared_6983_ = v_isSharedCheck_7001_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6980_);
                                v___x_6982_ = crate::leanh::lean_box(0);
                                v_isShared_6983_ = v_isSharedCheck_7001_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_alts_6978_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            return v___x_6980_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_alts_6978_);
                        crate::leanh::lean_dec(v_discr_6977_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_6979_;
                    }
                }
                5 => {
                    v_fvarId_7003_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7003_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 1);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7004_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7003_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_7004_;
                }
                6 => {
                    v_type_7005_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc_ref(v_type_7005_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 1);
                    v___x_7006_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6937_, v_type_7005_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                    return v___x_7006_;
                }
                7 => {
                    v_fvarId_7007_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7007_);
                    v_y_7008_ = crate::leanh::lean_ctor_get(v_c_6938_, 2);
                    crate::leanh::lean_inc(v_y_7008_);
                    v_k_7009_ = crate::leanh::lean_ctor_get(v_c_6938_, 3);
                    crate::leanh::lean_inc_ref(v_k_7009_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 4);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7010_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7007_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7010_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7010_, 1);
                        crate::leanh::lean_inc_ref(v_f_6937_);
                        v___x_7011_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_6937_, v_y_7008_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                        if crate::leanh::lean_obj_tag(v___x_7011_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7011_, 1);
                            v_c_6938_ = v_k_7009_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_7009_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            return v___x_7011_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7009_);
                        crate::leanh::lean_dec(v_y_7008_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7010_;
                    }
                }
                8 => {
                    v_fvarId_7013_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7013_);
                    v_y_7014_ = crate::leanh::lean_ctor_get(v_c_6938_, 2);
                    crate::leanh::lean_inc(v_y_7014_);
                    v_k_7015_ = crate::leanh::lean_ctor_get(v_c_6938_, 3);
                    crate::leanh::lean_inc_ref(v_k_7015_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 4);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7016_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7013_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7016_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7016_, 1);
                        crate::leanh::lean_inc_ref(v_f_6937_);
                        crate::leanh::lean_inc(v___y_6944_);
                        crate::leanh::lean_inc_ref(v___y_6943_);
                        crate::leanh::lean_inc(v___y_6942_);
                        crate::leanh::lean_inc_ref(v___y_6941_);
                        crate::leanh::lean_inc(v___y_6940_);
                        crate::leanh::lean_inc(v___y_6939_);
                        v___x_7017_ = crate::leanh::lean_apply_8(
                            v_f_6937_,
                            v_y_7014_,
                            v___y_6939_,
                            v___y_6940_,
                            v___y_6941_,
                            v___y_6942_,
                            v___y_6943_,
                            v___y_6944_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_7017_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7017_, 1);
                            v_c_6938_ = v_k_7015_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_k_7015_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            return v___x_7017_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7015_);
                        crate::leanh::lean_dec(v_y_7014_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7016_;
                    }
                }
                9 => {
                    v_fvarId_7019_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7019_);
                    v_y_7020_ = crate::leanh::lean_ctor_get(v_c_6938_, 3);
                    crate::leanh::lean_inc(v_y_7020_);
                    v_ty_7021_ = crate::leanh::lean_ctor_get(v_c_6938_, 4);
                    crate::leanh::lean_inc_ref(v_ty_7021_);
                    v_k_7022_ = crate::leanh::lean_ctor_get(v_c_6938_, 5);
                    crate::leanh::lean_inc_ref(v_k_7022_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 6);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7023_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7019_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7023_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7023_, 1);
                        crate::leanh::lean_inc_ref(v_f_6937_);
                        crate::leanh::lean_inc(v___y_6944_);
                        crate::leanh::lean_inc_ref(v___y_6943_);
                        crate::leanh::lean_inc(v___y_6942_);
                        crate::leanh::lean_inc_ref(v___y_6941_);
                        crate::leanh::lean_inc(v___y_6940_);
                        crate::leanh::lean_inc(v___y_6939_);
                        v___x_7024_ = crate::leanh::lean_apply_8(
                            v_f_6937_,
                            v_y_7020_,
                            v___y_6939_,
                            v___y_6940_,
                            v___y_6941_,
                            v___y_6942_,
                            v___y_6943_,
                            v___y_6944_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_7024_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7024_, 1);
                            crate::leanh::lean_inc_ref(v_f_6937_);
                            v___x_7025_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6937_, v_ty_7021_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                            if crate::leanh::lean_obj_tag(v___x_7025_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7025_, 1);
                                v_c_6938_ = v_k_7022_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_7022_);
                                crate::leanh::lean_dec_ref(v_f_6937_);
                                return v___x_7025_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_k_7022_);
                            crate::leanh::lean_dec_ref(v_ty_7021_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            return v___x_7024_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7022_);
                        crate::leanh::lean_dec_ref(v_ty_7021_);
                        crate::leanh::lean_dec(v_y_7020_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7023_;
                    }
                }
                10 => {
                    v_fvarId_7027_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7027_);
                    v_k_7028_ = crate::leanh::lean_ctor_get(v_c_6938_, 2);
                    crate::leanh::lean_inc_ref(v_k_7028_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 3);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7029_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7027_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7029_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7029_, 1);
                        v_c_6938_ = v_k_7028_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7028_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7029_;
                    }
                }
                11 => {
                    v_fvarId_7031_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7031_);
                    v_k_7032_ = crate::leanh::lean_ctor_get(v_c_6938_, 2);
                    crate::leanh::lean_inc_ref(v_k_7032_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 3);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7033_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7031_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7033_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7033_, 1);
                        v_c_6938_ = v_k_7032_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7032_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7033_;
                    }
                }
                12 => {
                    v_fvarId_7035_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7035_);
                    v_k_7036_ = crate::leanh::lean_ctor_get(v_c_6938_, 3);
                    crate::leanh::lean_inc_ref(v_k_7036_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 4);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7037_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7035_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7037_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7037_, 1);
                        v_c_6938_ = v_k_7036_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7036_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7037_;
                    }
                }
                13 => {
                    v_fvarId_7039_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc(v_fvarId_7039_);
                    v_k_7040_ = crate::leanh::lean_ctor_get(v_c_6938_, 1);
                    crate::leanh::lean_inc_ref(v_k_7040_);
                    crate::leanh::lean_dec_ref_known(v_c_6938_, 2);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    crate::leanh::lean_inc(v___y_6944_);
                    crate::leanh::lean_inc_ref(v___y_6943_);
                    crate::leanh::lean_inc(v___y_6942_);
                    crate::leanh::lean_inc_ref(v___y_6941_);
                    crate::leanh::lean_inc(v___y_6940_);
                    crate::leanh::lean_inc(v___y_6939_);
                    v___x_7041_ = crate::leanh::lean_apply_8(
                        v_f_6937_,
                        v_fvarId_7039_,
                        v___y_6939_,
                        v___y_6940_,
                        v___y_6941_,
                        v___y_6942_,
                        v___y_6943_,
                        v___y_6944_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7041_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7041_, 1);
                        v_c_6938_ = v_k_7040_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7040_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7041_;
                    }
                }
                _ => {
                    v_decl_7043_ = crate::leanh::lean_ctor_get(v_c_6938_, 0);
                    crate::leanh::lean_inc_ref(v_decl_7043_);
                    v_k_7044_ = crate::leanh::lean_ctor_get(v_c_6938_, 1);
                    crate::leanh::lean_inc_ref(v_k_7044_);
                    crate::leanh::lean_dec_ref(v_c_6938_);
                    v_params_7045_ = crate::leanh::lean_ctor_get(v_decl_7043_, 2);
                    crate::leanh::lean_inc_ref(v_params_7045_);
                    v_type_7046_ = crate::leanh::lean_ctor_get(v_decl_7043_, 3);
                    crate::leanh::lean_inc_ref(v_type_7046_);
                    v_value_7047_ = crate::leanh::lean_ctor_get(v_decl_7043_, 4);
                    crate::leanh::lean_inc_ref(v_value_7047_);
                    crate::leanh::lean_dec_ref(v_decl_7043_);
                    v___x_7058_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7059_ = lean_array_get_size(v_params_7045_);
                    v___x_7060_ = lean_nat_dec_lt(v___x_7058_, v___x_7059_);
                    if v___x_7060_ == 0 {
                        crate::leanh::lean_dec_ref(v_params_7045_);
                        crate::leanh::lean_inc_ref(v_f_6937_);
                        v___x_7061_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6937_, v_type_7046_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                        if crate::leanh::lean_obj_tag(v___x_7061_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7061_, 1);
                            crate::leanh::lean_inc_ref(v_f_6937_);
                            v___x_7062_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_6936_, v_f_6937_, v_value_7047_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                            if crate::leanh::lean_obj_tag(v___x_7062_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7062_, 1);
                                v_c_6938_ = v_k_7044_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_k_7044_);
                                crate::leanh::lean_dec_ref(v_f_6937_);
                                return v___x_7062_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_7047_);
                            crate::leanh::lean_dec_ref(v_k_7044_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            return v___x_7061_;
                        }
                    } else {
                        v___x_7064_ = crate::leanh::lean_box(0);
                        v___x_7065_ = lean_nat_dec_le(v___x_7059_, v___x_7059_);
                        if v___x_7065_ == 0 {
                            if v___x_7060_ == 0 {
                                crate::leanh::lean_dec_ref(v_params_7045_);
                                v___y_7049_ = v___y_6939_;
                                v___y_7050_ = v___y_6940_;
                                v___y_7051_ = v___y_6941_;
                                v___y_7052_ = v___y_6942_;
                                v___y_7053_ = v___y_6943_;
                                v___y_7054_ = v___y_6944_;
                                state = 7;
                                continue;
                            } else {
                                v___x_7066_ = 0usize;
                                v___x_7067_ = lean_usize_of_nat(v___x_7059_);
                                crate::leanh::lean_inc_ref(v_f_6937_);
                                v___x_7068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_6936_, v_f_6937_, v_params_7045_, v___x_7066_, v___x_7067_, v___x_7064_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                                crate::leanh::lean_dec_ref(v_params_7045_);
                                if crate::leanh::lean_obj_tag(v___x_7068_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_7068_, 1);
                                    v___y_7049_ = v___y_6939_;
                                    v___y_7050_ = v___y_6940_;
                                    v___y_7051_ = v___y_6941_;
                                    v___y_7052_ = v___y_6942_;
                                    v___y_7053_ = v___y_6943_;
                                    v___y_7054_ = v___y_6944_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_value_7047_);
                                    crate::leanh::lean_dec_ref(v_type_7046_);
                                    crate::leanh::lean_dec_ref(v_k_7044_);
                                    crate::leanh::lean_dec_ref(v_f_6937_);
                                    return v___x_7068_;
                                }
                            }
                        } else {
                            v___x_7069_ = 0usize;
                            v___x_7070_ = lean_usize_of_nat(v___x_7059_);
                            crate::leanh::lean_inc_ref(v_f_6937_);
                            v___x_7071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_6936_, v_f_6937_, v_params_7045_, v___x_7069_, v___x_7070_, v___x_7064_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                            crate::leanh::lean_dec_ref(v_params_7045_);
                            if crate::leanh::lean_obj_tag(v___x_7071_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7071_, 1);
                                v___y_7049_ = v___y_6939_;
                                v___y_7050_ = v___y_6940_;
                                v___y_7051_ = v___y_6941_;
                                v___y_7052_ = v___y_6942_;
                                v___y_7053_ = v___y_6943_;
                                v___y_7054_ = v___y_6944_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_value_7047_);
                                crate::leanh::lean_dec_ref(v_type_7046_);
                                crate::leanh::lean_dec_ref(v_k_7044_);
                                crate::leanh::lean_dec_ref(v_f_6937_);
                                return v___x_7071_;
                            }
                        }
                    }
                }
            },
            1 => {
                v___x_6956_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6957_ = lean_array_get_size(v_args_6951_);
                v___x_6958_ = crate::leanh::lean_box(0);
                v___x_6959_ = lean_nat_dec_lt(v___x_6956_, v___x_6957_);
                if v___x_6959_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_6951_);
                    crate::leanh::lean_dec_ref(v_f_6937_);
                    if v_isShared_6955_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6954_, 0, v___x_6958_);
                        v___x_6961_ = v___x_6954_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6962_, 0, v___x_6958_);
                        v___x_6961_ = v_reuseFailAlloc_6962_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6963_ = lean_nat_dec_le(v___x_6957_, v___x_6957_);
                    if v___x_6963_ == 0 {
                        if v___x_6959_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_6951_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            if v_isShared_6955_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6954_, 0, v___x_6958_);
                                v___x_6965_ = v___x_6954_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6966_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 0, v___x_6958_);
                                v___x_6965_ = v_reuseFailAlloc_6966_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6954_);
                            v___x_6967_ = 0usize;
                            v___x_6968_ = lean_usize_of_nat(v___x_6957_);
                            v___x_6969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6936_, v_f_6937_, v_args_6951_, v___x_6967_, v___x_6968_, v___x_6958_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                            crate::leanh::lean_dec_ref(v_args_6951_);
                            return v___x_6969_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6954_);
                        v___x_6970_ = 0usize;
                        v___x_6971_ = lean_usize_of_nat(v___x_6957_);
                        v___x_6972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_LetValue_forFVarM___at___00Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__2_spec__4(v_pu_6936_, v_f_6937_, v_args_6951_, v___x_6970_, v___x_6971_, v___x_6958_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                        crate::leanh::lean_dec_ref(v_args_6951_);
                        return v___x_6972_;
                    }
                }
            }
            2 => {
                return v___x_6961_;
            }
            3 => {
                return v___x_6965_;
            }
            4 => {
                v___x_6984_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6985_ = lean_array_get_size(v_alts_6978_);
                v___x_6986_ = crate::leanh::lean_box(0);
                v___x_6987_ = lean_nat_dec_lt(v___x_6984_, v___x_6985_);
                if v___x_6987_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_6978_);
                    crate::leanh::lean_dec_ref(v_f_6937_);
                    if v_isShared_6983_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6982_, 0, v___x_6986_);
                        v___x_6989_ = v___x_6982_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6990_, 0, v___x_6986_);
                        v___x_6989_ = v_reuseFailAlloc_6990_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_6991_ = lean_nat_dec_le(v___x_6985_, v___x_6985_);
                    if v___x_6991_ == 0 {
                        if v___x_6987_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_6978_);
                            crate::leanh::lean_dec_ref(v_f_6937_);
                            if v_isShared_6983_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6982_, 0, v___x_6986_);
                                v___x_6993_ = v___x_6982_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_6994_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6994_, 0, v___x_6986_);
                                v___x_6993_ = v_reuseFailAlloc_6994_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6982_);
                            v___x_6995_ = 0usize;
                            v___x_6996_ = lean_usize_of_nat(v___x_6985_);
                            v___x_6997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_6936_, v_f_6937_, v_alts_6978_, v___x_6995_, v___x_6996_, v___x_6986_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                            crate::leanh::lean_dec_ref(v_alts_6978_);
                            return v___x_6997_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6982_);
                        v___x_6998_ = 0usize;
                        v___x_6999_ = lean_usize_of_nat(v___x_6985_);
                        v___x_7000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_6936_, v_f_6937_, v_alts_6978_, v___x_6998_, v___x_6999_, v___x_6986_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_);
                        crate::leanh::lean_dec_ref(v_alts_6978_);
                        return v___x_7000_;
                    }
                }
            }
            5 => {
                return v___x_6989_;
            }
            6 => {
                return v___x_6993_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_f_6937_);
                v___x_7055_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_6937_, v_type_7046_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_);
                if crate::leanh::lean_obj_tag(v___x_7055_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7055_, 1);
                    crate::leanh::lean_inc_ref(v_f_6937_);
                    v___x_7056_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_6936_, v_f_6937_, v_value_7047_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_);
                    if crate::leanh::lean_obj_tag(v___x_7056_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7056_, 1);
                        v_c_6938_ = v_k_7044_;
                        v___y_6939_ = v___y_7049_;
                        v___y_6940_ = v___y_7050_;
                        v___y_6941_ = v___y_7051_;
                        v___y_6942_ = v___y_7052_;
                        v___y_6943_ = v___y_7053_;
                        v___y_6944_ = v___y_7054_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_7044_);
                        crate::leanh::lean_dec_ref(v_f_6937_);
                        return v___x_7056_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_7047_);
                    crate::leanh::lean_dec_ref(v_k_7044_);
                    crate::leanh::lean_dec_ref(v_f_6937_);
                    return v___x_7055_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___lam__0(
    mut v_pu_7072_: u8,
    mut v_f_7073_: *mut crate::leanh::LeanObject,
    mut v___y_7074_: *mut crate::leanh::LeanObject,
    mut v___y_7075_: *mut crate::leanh::LeanObject,
    mut v___y_7076_: *mut crate::leanh::LeanObject,
    mut v___y_7077_: *mut crate::leanh::LeanObject,
    mut v___y_7078_: *mut crate::leanh::LeanObject,
    mut v___y_7079_: *mut crate::leanh::LeanObject,
    mut v___y_7080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7082_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_7072_, v_f_7073_, v___y_7074_, v___y_7075_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_, v___y_7080_);
    return v___x_7082_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9___boxed(
    mut v_pu_7083_: *mut crate::leanh::LeanObject,
    mut v_f_7084_: *mut crate::leanh::LeanObject,
    mut v_as_7085_: *mut crate::leanh::LeanObject,
    mut v_i_7086_: *mut crate::leanh::LeanObject,
    mut v_stop_7087_: *mut crate::leanh::LeanObject,
    mut v_b_7088_: *mut crate::leanh::LeanObject,
    mut v___y_7089_: *mut crate::leanh::LeanObject,
    mut v___y_7090_: *mut crate::leanh::LeanObject,
    mut v___y_7091_: *mut crate::leanh::LeanObject,
    mut v___y_7092_: *mut crate::leanh::LeanObject,
    mut v___y_7093_: *mut crate::leanh::LeanObject,
    mut v___y_7094_: *mut crate::leanh::LeanObject,
    mut v___y_7095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7096_: u8 = 0;
    let mut v_i_boxed_7097_: usize = 0;
    let mut v_stop_boxed_7098_: usize = 0;
    let mut v_res_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7096_ = (crate::leanh::lean_unbox(v_pu_7083_) as u8);
    v_i_boxed_7097_ = crate::leanh::lean_unbox_usize(v_i_7086_);
    crate::leanh::lean_dec(v_i_7086_);
    v_stop_boxed_7098_ = crate::leanh::lean_unbox_usize(v_stop_7087_);
    crate::leanh::lean_dec(v_stop_7087_);
    v_res_7099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__9(v_pu_boxed_7096_, v_f_7084_, v_as_7085_, v_i_boxed_7097_, v_stop_boxed_7098_, v_b_7088_, v___y_7089_, v___y_7090_, v___y_7091_, v___y_7092_, v___y_7093_, v___y_7094_);
    crate::leanh::lean_dec(v___y_7094_);
    crate::leanh::lean_dec_ref(v___y_7093_);
    crate::leanh::lean_dec(v___y_7092_);
    crate::leanh::lean_dec_ref(v___y_7091_);
    crate::leanh::lean_dec(v___y_7090_);
    crate::leanh::lean_dec(v___y_7089_);
    crate::leanh::lean_dec_ref(v_as_7085_);
    return v_res_7099_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5___boxed(
    mut v_pu_7100_: *mut crate::leanh::LeanObject,
    mut v_f_7101_: *mut crate::leanh::LeanObject,
    mut v_c_7102_: *mut crate::leanh::LeanObject,
    mut v___y_7103_: *mut crate::leanh::LeanObject,
    mut v___y_7104_: *mut crate::leanh::LeanObject,
    mut v___y_7105_: *mut crate::leanh::LeanObject,
    mut v___y_7106_: *mut crate::leanh::LeanObject,
    mut v___y_7107_: *mut crate::leanh::LeanObject,
    mut v___y_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7110_: u8 = 0;
    let mut v_res_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7110_ = (crate::leanh::lean_unbox(v_pu_7100_) as u8);
    v_res_7111_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_boxed_7110_, v_f_7101_, v_c_7102_, v___y_7103_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_);
    crate::leanh::lean_dec(v___y_7108_);
    crate::leanh::lean_dec_ref(v___y_7107_);
    crate::leanh::lean_dec(v___y_7106_);
    crate::leanh::lean_dec_ref(v___y_7105_);
    crate::leanh::lean_dec(v___y_7104_);
    crate::leanh::lean_dec(v___y_7103_);
    return v_res_7111_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(
    mut v_pu_7112_: u8,
    mut v_f_7113_: *mut crate::leanh::LeanObject,
    mut v_decl_7114_: *mut crate::leanh::LeanObject,
    mut v___y_7115_: *mut crate::leanh::LeanObject,
    mut v___y_7116_: *mut crate::leanh::LeanObject,
    mut v___y_7117_: *mut crate::leanh::LeanObject,
    mut v___y_7118_: *mut crate::leanh::LeanObject,
    mut v___y_7119_: *mut crate::leanh::LeanObject,
    mut v___y_7120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: u8 = 0;
    let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: u8 = 0;
    let mut v___x_7141_: usize = 0;
    let mut v___x_7142_: usize = 0;
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: usize = 0;
    let mut v___x_7145_: usize = 0;
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_7122_ = crate::leanh::lean_ctor_get(v_decl_7114_, 2);
                crate::leanh::lean_inc_ref(v_params_7122_);
                v_type_7123_ = crate::leanh::lean_ctor_get(v_decl_7114_, 3);
                crate::leanh::lean_inc_ref(v_type_7123_);
                v_value_7124_ = crate::leanh::lean_ctor_get(v_decl_7114_, 4);
                crate::leanh::lean_inc_ref(v_value_7124_);
                crate::leanh::lean_dec_ref(v_decl_7114_);
                v___x_7134_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7135_ = lean_array_get_size(v_params_7122_);
                v___x_7136_ = lean_nat_dec_lt(v___x_7134_, v___x_7135_);
                if v___x_7136_ == 0 {
                    crate::leanh::lean_dec_ref(v_params_7122_);
                    crate::leanh::lean_inc_ref(v_f_7113_);
                    v___x_7137_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_7113_, v_type_7123_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_);
                    if crate::leanh::lean_obj_tag(v___x_7137_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7137_, 1);
                        v___x_7138_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_7112_, v_f_7113_, v_value_7124_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_);
                        return v___x_7138_;
                    } else {
                        crate::leanh::lean_dec_ref(v_value_7124_);
                        crate::leanh::lean_dec_ref(v_f_7113_);
                        return v___x_7137_;
                    }
                } else {
                    v___x_7139_ = crate::leanh::lean_box(0);
                    v___x_7140_ = lean_nat_dec_le(v___x_7135_, v___x_7135_);
                    if v___x_7140_ == 0 {
                        if v___x_7136_ == 0 {
                            crate::leanh::lean_dec_ref(v_params_7122_);
                            v___y_7126_ = v___y_7115_;
                            v___y_7127_ = v___y_7116_;
                            v___y_7128_ = v___y_7117_;
                            v___y_7129_ = v___y_7118_;
                            v___y_7130_ = v___y_7119_;
                            v___y_7131_ = v___y_7120_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7141_ = 0usize;
                            v___x_7142_ = lean_usize_of_nat(v___x_7135_);
                            crate::leanh::lean_inc_ref(v_f_7113_);
                            v___x_7143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_7112_, v_f_7113_, v_params_7122_, v___x_7141_, v___x_7142_, v___x_7139_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_);
                            crate::leanh::lean_dec_ref(v_params_7122_);
                            if crate::leanh::lean_obj_tag(v___x_7143_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7143_, 1);
                                v___y_7126_ = v___y_7115_;
                                v___y_7127_ = v___y_7116_;
                                v___y_7128_ = v___y_7117_;
                                v___y_7129_ = v___y_7118_;
                                v___y_7130_ = v___y_7119_;
                                v___y_7131_ = v___y_7120_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_value_7124_);
                                crate::leanh::lean_dec_ref(v_type_7123_);
                                crate::leanh::lean_dec_ref(v_f_7113_);
                                return v___x_7143_;
                            }
                        }
                    } else {
                        v___x_7144_ = 0usize;
                        v___x_7145_ = lean_usize_of_nat(v___x_7135_);
                        crate::leanh::lean_inc_ref(v_f_7113_);
                        v___x_7146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__6(v_pu_7112_, v_f_7113_, v_params_7122_, v___x_7144_, v___x_7145_, v___x_7139_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_);
                        crate::leanh::lean_dec_ref(v_params_7122_);
                        if crate::leanh::lean_obj_tag(v___x_7146_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7146_, 1);
                            v___y_7126_ = v___y_7115_;
                            v___y_7127_ = v___y_7116_;
                            v___y_7128_ = v___y_7117_;
                            v___y_7129_ = v___y_7118_;
                            v___y_7130_ = v___y_7119_;
                            v___y_7131_ = v___y_7120_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_value_7124_);
                            crate::leanh::lean_dec_ref(v_type_7123_);
                            crate::leanh::lean_dec_ref(v_f_7113_);
                            return v___x_7146_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_7113_);
                v___x_7132_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v_f_7113_, v_type_7123_, v___y_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_, v___y_7131_);
                if crate::leanh::lean_obj_tag(v___x_7132_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7132_, 1);
                    v___x_7133_ = l_Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5(v_pu_7112_, v_f_7113_, v_value_7124_, v___y_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_, v___y_7131_);
                    return v___x_7133_;
                } else {
                    crate::leanh::lean_dec_ref(v_value_7124_);
                    crate::leanh::lean_dec_ref(v_f_7113_);
                    return v___x_7132_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2___boxed(
    mut v_pu_7147_: *mut crate::leanh::LeanObject,
    mut v_f_7148_: *mut crate::leanh::LeanObject,
    mut v_decl_7149_: *mut crate::leanh::LeanObject,
    mut v___y_7150_: *mut crate::leanh::LeanObject,
    mut v___y_7151_: *mut crate::leanh::LeanObject,
    mut v___y_7152_: *mut crate::leanh::LeanObject,
    mut v___y_7153_: *mut crate::leanh::LeanObject,
    mut v___y_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
    mut v___y_7156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7157_: u8 = 0;
    let mut v_res_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7157_ = (crate::leanh::lean_unbox(v_pu_7147_) as u8);
    v_res_7158_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v_pu_boxed_7157_, v_f_7148_, v_decl_7149_, v___y_7150_, v___y_7151_, v___y_7152_, v___y_7153_, v___y_7154_, v___y_7155_);
    crate::leanh::lean_dec(v___y_7155_);
    crate::leanh::lean_dec_ref(v___y_7154_);
    crate::leanh::lean_dec(v___y_7153_);
    crate::leanh::lean_dec_ref(v___y_7152_);
    crate::leanh::lean_dec(v___y_7151_);
    crate::leanh::lean_dec(v___y_7150_);
    return v_res_7158_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(
    mut v_msg_7159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7160_ = crate::leanh::lean_box(0);
    v___x_7161_ = lean_panic_fn_borrowed(v___x_7160_, v_msg_7159_);
    return v___x_7161_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7165_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__2;
    v___x_7166_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_7167_ = crate::leanh::lean_unsigned_to_nat(163);
    v___x_7168_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__1;
    v___x_7169_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__0;
    v___x_7170_ = l_mkPanicMessageWithDecl(
        v___x_7169_,
        v___x_7168_,
        v___x_7167_,
        v___x_7166_,
        v___x_7165_,
    );
    return v___x_7170_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(
    mut v_a_7171_: *mut crate::leanh::LeanObject,
    mut v_x_7172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7172_) == 0 {
                    v___x_7173_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
                    v___x_7174_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0_spec__1(v___x_7173_);
                    return v___x_7174_;
                } else {
                    v_key_7175_ = crate::leanh::lean_ctor_get(v_x_7172_, 0);
                    v_value_7176_ = crate::leanh::lean_ctor_get(v_x_7172_, 1);
                    v_tail_7177_ = crate::leanh::lean_ctor_get(v_x_7172_, 2);
                    v___x_7178_ =
                        l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_key_7175_, v_a_7171_);
                    if v___x_7178_ == 0 {
                        v_x_7172_ = v_tail_7177_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_7176_);
                        return v_value_7176_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___boxed(
    mut v_a_7180_: *mut crate::leanh::LeanObject,
    mut v_x_7181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7182_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_7180_, v_x_7181_);
    crate::leanh::lean_dec(v_x_7181_);
    crate::leanh::lean_dec(v_a_7180_);
    return v_res_7182_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(
    mut v_m_7183_: *mut crate::leanh::LeanObject,
    mut v_a_7184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: u64 = 0;
    let mut v___x_7188_: u64 = 0;
    let mut v___x_7189_: u64 = 0;
    let mut v_fold_7190_: u64 = 0;
    let mut v___x_7191_: u64 = 0;
    let mut v___x_7192_: u64 = 0;
    let mut v___x_7193_: u64 = 0;
    let mut v___x_7194_: usize = 0;
    let mut v___x_7195_: usize = 0;
    let mut v___x_7196_: usize = 0;
    let mut v___x_7197_: usize = 0;
    let mut v___x_7198_: usize = 0;
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_7185_ = crate::leanh::lean_ctor_get(v_m_7183_, 1);
    v___x_7186_ = lean_array_get_size(v_buckets_7185_);
    v___x_7187_ = l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision_hash(v_a_7184_);
    v___x_7188_ = 32u64;
    v___x_7189_ = lean_uint64_shift_right(v___x_7187_, v___x_7188_);
    v_fold_7190_ = lean_uint64_xor(v___x_7187_, v___x_7189_);
    v___x_7191_ = 16u64;
    v___x_7192_ = lean_uint64_shift_right(v_fold_7190_, v___x_7191_);
    v___x_7193_ = lean_uint64_xor(v_fold_7190_, v___x_7192_);
    v___x_7194_ = lean_uint64_to_usize(v___x_7193_);
    v___x_7195_ = lean_usize_of_nat(v___x_7186_);
    v___x_7196_ = 1usize;
    v___x_7197_ = lean_usize_sub(v___x_7195_, v___x_7196_);
    v___x_7198_ = lean_usize_land(v___x_7194_, v___x_7197_);
    v___x_7199_ = lean_array_uget_borrowed(v_buckets_7185_, v___x_7198_);
    v___x_7200_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0(v_a_7184_, v___x_7199_);
    return v___x_7200_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(
    mut v_m_7201_: *mut crate::leanh::LeanObject,
    mut v_a_7202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_m_7201_, v_a_7202_);
    crate::leanh::lean_dec(v_a_7202_);
    crate::leanh::lean_dec_ref(v_m_7201_);
    return v_res_7203_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(
    mut v_decl_7205_: *mut crate::leanh::LeanObject,
    mut v_a_7206_: *mut crate::leanh::LeanObject,
    mut v_a_7207_: *mut crate::leanh::LeanObject,
    mut v_a_7208_: *mut crate::leanh::LeanObject,
    mut v_a_7209_: *mut crate::leanh::LeanObject,
    mut v_a_7210_: *mut crate::leanh::LeanObject,
    mut v_a_7211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7217_: u8 = 0;
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArms_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7223_: u8 = 0;
    let mut v___x_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7236_: u8 = 0;
    let mut v_isSharedCheck_7237_: u8 = 0;
    let mut v_unused_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: u8 = 0;
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7239_ = 0;
                v___x_7240_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___closed__0;
                match crate::leanh::lean_obj_tag(v_decl_7205_) {
                    0 => {
                        v_decl_7241_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        crate::leanh::lean_inc_ref(v_decl_7241_);
                        v___x_7242_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_7239_, v___x_7240_, v_decl_7241_, v_a_7206_, v_a_7207_, v_a_7208_, v_a_7209_, v_a_7210_, v_a_7211_);
                        v___y_7214_ = v___x_7242_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_decl_7243_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        crate::leanh::lean_inc_ref(v_decl_7243_);
                        v___x_7244_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_7239_, v___x_7240_, v_decl_7243_, v_a_7206_, v_a_7207_, v_a_7208_, v_a_7209_, v_a_7210_, v_a_7211_);
                        v___y_7214_ = v___x_7244_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v_decl_7245_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        crate::leanh::lean_inc_ref(v_decl_7245_);
                        v___x_7246_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_7239_, v___x_7240_, v_decl_7245_, v_a_7206_, v_a_7207_, v_a_7208_, v_a_7209_, v_a_7210_, v_a_7211_);
                        v___y_7214_ = v___x_7246_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_fvarId_7247_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        v_y_7248_ = crate::leanh::lean_ctor_get(v_decl_7205_, 2);
                        crate::leanh::lean_inc(v_fvarId_7247_);
                        v___x_7249_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_7247_, v_a_7206_);
                        crate::leanh::lean_dec_ref(v___x_7249_);
                        crate::leanh::lean_inc(v_y_7248_);
                        v___x_7250_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___x_7240_, v_y_7248_, v_a_7206_, v_a_7207_, v_a_7208_, v_a_7209_, v_a_7210_, v_a_7211_);
                        v___y_7214_ = v___x_7250_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_fvarId_7251_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        v_y_7252_ = crate::leanh::lean_ctor_get(v_decl_7205_, 2);
                        crate::leanh::lean_inc(v_fvarId_7251_);
                        v___x_7253_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_7251_, v_a_7206_);
                        crate::leanh::lean_dec_ref(v___x_7253_);
                        crate::leanh::lean_inc(v_y_7252_);
                        v___x_7254_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_7252_, v_a_7206_);
                        v___y_7214_ = v___x_7254_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_fvarId_7255_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        v_y_7256_ = crate::leanh::lean_ctor_get(v_decl_7205_, 3);
                        v_ty_7257_ = crate::leanh::lean_ctor_get(v_decl_7205_, 4);
                        crate::leanh::lean_inc(v_fvarId_7255_);
                        v___x_7258_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_7255_, v_a_7206_);
                        crate::leanh::lean_dec_ref(v___x_7258_);
                        crate::leanh::lean_inc(v_y_7256_);
                        v___x_7259_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_y_7256_, v_a_7206_);
                        crate::leanh::lean_dec_ref(v___x_7259_);
                        crate::leanh::lean_inc_ref(v_ty_7257_);
                        v___x_7260_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___x_7240_, v_ty_7257_, v_a_7206_, v_a_7207_, v_a_7208_, v_a_7209_, v_a_7210_, v_a_7211_);
                        v___y_7214_ = v___x_7260_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_fvarId_7261_ = crate::leanh::lean_ctor_get(v_decl_7205_, 0);
                        crate::leanh::lean_inc(v_fvarId_7261_);
                        v___x_7262_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(v_fvarId_7261_, v_a_7206_);
                        v___y_7214_ = v___x_7262_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_7214_) == 0 {
                    v_isSharedCheck_7237_ = (!crate::leanh::lean_is_exclusive(v___y_7214_)) as u8;
                    if v_isSharedCheck_7237_ == 0 {
                        v_unused_7238_ = crate::leanh::lean_ctor_get(v___y_7214_, 0);
                        crate::leanh::lean_dec(v_unused_7238_);
                        v___x_7216_ = v___y_7214_;
                        v_isShared_7217_ = v_isSharedCheck_7237_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_7214_);
                        v___x_7216_ = crate::leanh::lean_box(0);
                        v_isShared_7217_ = v_isSharedCheck_7237_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decl_7205_);
                    return v___y_7214_;
                }
            }
            2 => {
                v___x_7218_ = lean_st_ref_take(v_a_7206_);
                v_decision_7219_ = crate::leanh::lean_ctor_get(v___x_7218_, 0);
                v_newArms_7220_ = crate::leanh::lean_ctor_get(v___x_7218_, 1);
                v_isSharedCheck_7236_ = (!crate::leanh::lean_is_exclusive(v___x_7218_)) as u8;
                if v_isSharedCheck_7236_ == 0 {
                    v___x_7222_ = v___x_7218_;
                    v_isShared_7223_ = v_isSharedCheck_7236_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_newArms_7220_);
                    crate::leanh::lean_inc(v_decision_7219_);
                    crate::leanh::lean_dec(v___x_7218_);
                    v___x_7222_ = crate::leanh::lean_box(0);
                    v_isShared_7223_ = v_isSharedCheck_7236_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7224_ = crate::leanh::lean_box(2);
                v___x_7225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_7220_, v___x_7224_);
                v___x_7226_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7226_, 0, v_decl_7205_);
                crate::leanh::lean_ctor_set(v___x_7226_, 1, v___x_7225_);
                v___x_7227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_7220_, v___x_7224_, v___x_7226_);
                if v_isShared_7223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7222_, 1, v___x_7227_);
                    v___x_7229_ = v___x_7222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7235_, 0, v_decision_7219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7235_, 1, v___x_7227_);
                    v___x_7229_ = v_reuseFailAlloc_7235_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7230_ = lean_st_ref_set(v_a_7206_, v___x_7229_);
                v___x_7231_ = crate::leanh::lean_box(0);
                if v_isShared_7217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7216_, 0, v___x_7231_);
                    v___x_7233_ = v___x_7216_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7234_, 0, v___x_7231_);
                    v___x_7233_ = v_reuseFailAlloc_7234_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_dontFloat___boxed(
    mut v_decl_7263_: *mut crate::leanh::LeanObject,
    mut v_a_7264_: *mut crate::leanh::LeanObject,
    mut v_a_7265_: *mut crate::leanh::LeanObject,
    mut v_a_7266_: *mut crate::leanh::LeanObject,
    mut v_a_7267_: *mut crate::leanh::LeanObject,
    mut v_a_7268_: *mut crate::leanh::LeanObject,
    mut v_a_7269_: *mut crate::leanh::LeanObject,
    mut v_a_7270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7271_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(
        v_decl_7263_,
        v_a_7264_,
        v_a_7265_,
        v_a_7266_,
        v_a_7267_,
        v_a_7268_,
        v_a_7269_,
    );
    crate::leanh::lean_dec(v_a_7269_);
    crate::leanh::lean_dec_ref(v_a_7268_);
    crate::leanh::lean_dec(v_a_7267_);
    crate::leanh::lean_dec_ref(v_a_7266_);
    crate::leanh::lean_dec(v_a_7265_);
    crate::leanh::lean_dec(v_a_7264_);
    return v_res_7271_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(
    mut v_pu_7272_: u8,
    mut v_f_7273_: *mut crate::leanh::LeanObject,
    mut v_arg_7274_: *mut crate::leanh::LeanObject,
    mut v___y_7275_: *mut crate::leanh::LeanObject,
    mut v___y_7276_: *mut crate::leanh::LeanObject,
    mut v___y_7277_: *mut crate::leanh::LeanObject,
    mut v___y_7278_: *mut crate::leanh::LeanObject,
    mut v___y_7279_: *mut crate::leanh::LeanObject,
    mut v___y_7280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7282_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v_f_7273_, v_arg_7274_, v___y_7275_, v___y_7276_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
    return v___x_7282_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___boxed(
    mut v_pu_7283_: *mut crate::leanh::LeanObject,
    mut v_f_7284_: *mut crate::leanh::LeanObject,
    mut v_arg_7285_: *mut crate::leanh::LeanObject,
    mut v___y_7286_: *mut crate::leanh::LeanObject,
    mut v___y_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
    mut v___y_7291_: *mut crate::leanh::LeanObject,
    mut v___y_7292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7293_: u8 = 0;
    let mut v_res_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7293_ = (crate::leanh::lean_unbox(v_pu_7283_) as u8);
    v_res_7294_ =
        l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3(
            v_pu_boxed_7293_,
            v_f_7284_,
            v_arg_7285_,
            v___y_7286_,
            v___y_7287_,
            v___y_7288_,
            v___y_7289_,
            v___y_7290_,
            v___y_7291_,
        );
    crate::leanh::lean_dec(v___y_7291_);
    crate::leanh::lean_dec_ref(v___y_7290_);
    crate::leanh::lean_dec(v___y_7289_);
    crate::leanh::lean_dec_ref(v___y_7288_);
    crate::leanh::lean_dec(v___y_7287_);
    crate::leanh::lean_dec(v___y_7286_);
    return v_res_7294_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(
    mut v_pu_7295_: u8,
    mut v_f_7296_: *mut crate::leanh::LeanObject,
    mut v_param_7297_: *mut crate::leanh::LeanObject,
    mut v___y_7298_: *mut crate::leanh::LeanObject,
    mut v___y_7299_: *mut crate::leanh::LeanObject,
    mut v___y_7300_: *mut crate::leanh::LeanObject,
    mut v___y_7301_: *mut crate::leanh::LeanObject,
    mut v___y_7302_: *mut crate::leanh::LeanObject,
    mut v___y_7303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7305_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___redArg(v_f_7296_, v_param_7297_, v___y_7298_, v___y_7299_, v___y_7300_, v___y_7301_, v___y_7302_, v___y_7303_);
    return v___x_7305_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4___boxed(
    mut v_pu_7306_: *mut crate::leanh::LeanObject,
    mut v_f_7307_: *mut crate::leanh::LeanObject,
    mut v_param_7308_: *mut crate::leanh::LeanObject,
    mut v___y_7309_: *mut crate::leanh::LeanObject,
    mut v___y_7310_: *mut crate::leanh::LeanObject,
    mut v___y_7311_: *mut crate::leanh::LeanObject,
    mut v___y_7312_: *mut crate::leanh::LeanObject,
    mut v___y_7313_: *mut crate::leanh::LeanObject,
    mut v___y_7314_: *mut crate::leanh::LeanObject,
    mut v___y_7315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7316_: u8 = 0;
    let mut v_res_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7316_ = (crate::leanh::lean_unbox(v_pu_7306_) as u8);
    v_res_7317_ = l_Lean_Compiler_LCNF_Param_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__4(v_pu_boxed_7316_, v_f_7307_, v_param_7308_, v___y_7309_, v___y_7310_, v___y_7311_, v___y_7312_, v___y_7313_, v___y_7314_);
    crate::leanh::lean_dec(v___y_7314_);
    crate::leanh::lean_dec_ref(v___y_7313_);
    crate::leanh::lean_dec(v___y_7312_);
    crate::leanh::lean_dec_ref(v___y_7311_);
    crate::leanh::lean_dec(v___y_7310_);
    crate::leanh::lean_dec(v___y_7309_);
    return v_res_7317_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(
    mut v_pu_7318_: u8,
    mut v_alt_7319_: *mut crate::leanh::LeanObject,
    mut v_f_7320_: *mut crate::leanh::LeanObject,
    mut v___y_7321_: *mut crate::leanh::LeanObject,
    mut v___y_7322_: *mut crate::leanh::LeanObject,
    mut v___y_7323_: *mut crate::leanh::LeanObject,
    mut v___y_7324_: *mut crate::leanh::LeanObject,
    mut v___y_7325_: *mut crate::leanh::LeanObject,
    mut v___y_7326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7328_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___redArg(v_alt_7319_, v_f_7320_, v___y_7321_, v___y_7322_, v___y_7323_, v___y_7324_, v___y_7325_, v___y_7326_);
    return v___x_7328_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8___boxed(
    mut v_pu_7329_: *mut crate::leanh::LeanObject,
    mut v_alt_7330_: *mut crate::leanh::LeanObject,
    mut v_f_7331_: *mut crate::leanh::LeanObject,
    mut v___y_7332_: *mut crate::leanh::LeanObject,
    mut v___y_7333_: *mut crate::leanh::LeanObject,
    mut v___y_7334_: *mut crate::leanh::LeanObject,
    mut v___y_7335_: *mut crate::leanh::LeanObject,
    mut v___y_7336_: *mut crate::leanh::LeanObject,
    mut v___y_7337_: *mut crate::leanh::LeanObject,
    mut v___y_7338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7339_: u8 = 0;
    let mut v_res_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7339_ = (crate::leanh::lean_unbox(v_pu_7329_) as u8);
    v_res_7340_ = l_Lean_Compiler_LCNF_Alt_forCodeM___at___00Lean_Compiler_LCNF_Code_forFVarM___at___00Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2_spec__5_spec__8(v_pu_boxed_7339_, v_alt_7330_, v_f_7331_, v___y_7332_, v___y_7333_, v___y_7334_, v___y_7335_, v___y_7336_, v___y_7337_);
    crate::leanh::lean_dec(v___y_7337_);
    crate::leanh::lean_dec_ref(v___y_7336_);
    crate::leanh::lean_dec(v___y_7335_);
    crate::leanh::lean_dec_ref(v___y_7334_);
    crate::leanh::lean_dec(v___y_7333_);
    crate::leanh::lean_dec(v___y_7332_);
    return v_res_7340_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(
    mut v_fvar_7341_: *mut crate::leanh::LeanObject,
    mut v_arm_7342_: *mut crate::leanh::LeanObject,
    mut v_a_7343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArms_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7352_: u8 = 0;
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7361_: u8 = 0;
    let mut v_decision_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7367_: u8 = 0;
    let mut v___x_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: u8 = 0;
    let mut v___x_7370_: u8 = 0;
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArms_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7380_: u8 = 0;
    let mut v___x_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7390_: u8 = 0;
    let mut v_isSharedCheck_7391_: u8 = 0;
    let mut v___x_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7345_ = lean_st_ref_get(v_a_7343_);
                v_decision_7362_ = crate::leanh::lean_ctor_get(v___x_7345_, 0);
                crate::leanh::lean_inc_ref(v_decision_7362_);
                crate::leanh::lean_dec(v___x_7345_);
                v___x_7363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__0___redArg(v_decision_7362_, v_fvar_7341_);
                crate::leanh::lean_dec_ref(v_decision_7362_);
                if crate::leanh::lean_obj_tag(v___x_7363_) == 1 {
                    v_val_7364_ = crate::leanh::lean_ctor_get(v___x_7363_, 0);
                    v_isSharedCheck_7391_ = (!crate::leanh::lean_is_exclusive(v___x_7363_)) as u8;
                    if v_isSharedCheck_7391_ == 0 {
                        v___x_7366_ = v___x_7363_;
                        v_isShared_7367_ = v_isSharedCheck_7391_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7364_);
                        crate::leanh::lean_dec(v___x_7363_);
                        v___x_7366_ = crate::leanh::lean_box(0);
                        v_isShared_7367_ = v_isSharedCheck_7391_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7363_);
                    crate::leanh::lean_dec(v_arm_7342_);
                    crate::leanh::lean_dec(v_fvar_7341_);
                    v___x_7392_ = crate::leanh::lean_box(0);
                    v___x_7393_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7393_, 0, v___x_7392_);
                    return v___x_7393_;
                }
            }
            1 => {
                v___x_7347_ = lean_st_ref_take(v_a_7343_);
                v_decision_7348_ = crate::leanh::lean_ctor_get(v___x_7347_, 0);
                v_newArms_7349_ = crate::leanh::lean_ctor_get(v___x_7347_, 1);
                v_isSharedCheck_7361_ = (!crate::leanh::lean_is_exclusive(v___x_7347_)) as u8;
                if v_isSharedCheck_7361_ == 0 {
                    v___x_7351_ = v___x_7347_;
                    v_isShared_7352_ = v_isSharedCheck_7361_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_newArms_7349_);
                    crate::leanh::lean_inc(v_decision_7348_);
                    crate::leanh::lean_dec(v___x_7347_);
                    v___x_7351_ = crate::leanh::lean_box(0);
                    v_isShared_7352_ = v_isSharedCheck_7361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7353_ = crate::leanh::lean_box(2);
                v___x_7354_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_7348_, v_fvar_7341_, v___x_7353_);
                if v_isShared_7352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7351_, 0, v___x_7354_);
                    v___x_7356_ = v___x_7351_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7360_, 0, v___x_7354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7360_, 1, v_newArms_7349_);
                    v___x_7356_ = v_reuseFailAlloc_7360_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7357_ = lean_st_ref_set(v_a_7343_, v___x_7356_);
                v___x_7358_ = crate::leanh::lean_box(0);
                v___x_7359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7359_, 0, v___x_7358_);
                return v___x_7359_;
            }
            4 => {
                v___x_7368_ = crate::leanh::lean_box(3);
                v___x_7369_ =
                    l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(v_val_7364_, v___x_7368_);
                if v___x_7369_ == 0 {
                    v___x_7370_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(
                        v_val_7364_,
                        v_arm_7342_,
                    );
                    crate::leanh::lean_dec(v_arm_7342_);
                    crate::leanh::lean_dec(v_val_7364_);
                    if v___x_7370_ == 0 {
                        crate::leanh::lean_del_object(v___x_7366_);
                        state = 1;
                        continue;
                    } else {
                        if v___x_7369_ == 0 {
                            crate::leanh::lean_dec(v_fvar_7341_);
                            v___x_7371_ = crate::leanh::lean_box(0);
                            if v_isShared_7367_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_7366_, 0);
                                crate::leanh::lean_ctor_set(v___x_7366_, 0, v___x_7371_);
                                v___x_7373_ = v___x_7366_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_7374_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7374_, 0, v___x_7371_);
                                v___x_7373_ = v_reuseFailAlloc_7374_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7366_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_7364_);
                    v___x_7375_ = lean_st_ref_take(v_a_7343_);
                    v_decision_7376_ = crate::leanh::lean_ctor_get(v___x_7375_, 0);
                    v_newArms_7377_ = crate::leanh::lean_ctor_get(v___x_7375_, 1);
                    v_isSharedCheck_7390_ = (!crate::leanh::lean_is_exclusive(v___x_7375_)) as u8;
                    if v_isSharedCheck_7390_ == 0 {
                        v___x_7379_ = v___x_7375_;
                        v_isShared_7380_ = v_isSharedCheck_7390_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_newArms_7377_);
                        crate::leanh::lean_inc(v_decision_7376_);
                        crate::leanh::lean_dec(v___x_7375_);
                        v___x_7379_ = crate::leanh::lean_box(0);
                        v_isShared_7380_ = v_isSharedCheck_7390_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_7373_;
            }
            6 => {
                v___x_7381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar_spec__1___redArg(v_decision_7376_, v_fvar_7341_, v_arm_7342_);
                if v_isShared_7380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7379_, 0, v___x_7381_);
                    v___x_7383_ = v___x_7379_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7389_, 0, v___x_7381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7389_, 1, v_newArms_7377_);
                    v___x_7383_ = v_reuseFailAlloc_7389_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_7384_ = lean_st_ref_set(v_a_7343_, v___x_7383_);
                v___x_7385_ = crate::leanh::lean_box(0);
                if v_isShared_7367_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7366_, 0);
                    crate::leanh::lean_ctor_set(v___x_7366_, 0, v___x_7385_);
                    v___x_7387_ = v___x_7366_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7388_, 0, v___x_7385_);
                    v___x_7387_ = v_reuseFailAlloc_7388_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(
    mut v_fvar_7394_: *mut crate::leanh::LeanObject,
    mut v_arm_7395_: *mut crate::leanh::LeanObject,
    mut v_a_7396_: *mut crate::leanh::LeanObject,
    mut v_a_7397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7398_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_7394_, v_arm_7395_, v_a_7396_);
    crate::leanh::lean_dec(v_a_7396_);
    return v_res_7398_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(
    mut v_fvar_7399_: *mut crate::leanh::LeanObject,
    mut v_arm_7400_: *mut crate::leanh::LeanObject,
    mut v_a_7401_: *mut crate::leanh::LeanObject,
    mut v_a_7402_: *mut crate::leanh::LeanObject,
    mut v_a_7403_: *mut crate::leanh::LeanObject,
    mut v_a_7404_: *mut crate::leanh::LeanObject,
    mut v_a_7405_: *mut crate::leanh::LeanObject,
    mut v_a_7406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7408_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvar_7399_, v_arm_7400_, v_a_7401_);
    return v___x_7408_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(
    mut v_fvar_7409_: *mut crate::leanh::LeanObject,
    mut v_arm_7410_: *mut crate::leanh::LeanObject,
    mut v_a_7411_: *mut crate::leanh::LeanObject,
    mut v_a_7412_: *mut crate::leanh::LeanObject,
    mut v_a_7413_: *mut crate::leanh::LeanObject,
    mut v_a_7414_: *mut crate::leanh::LeanObject,
    mut v_a_7415_: *mut crate::leanh::LeanObject,
    mut v_a_7416_: *mut crate::leanh::LeanObject,
    mut v_a_7417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7418_ =
        l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar(
            v_fvar_7409_,
            v_arm_7410_,
            v_a_7411_,
            v_a_7412_,
            v_a_7413_,
            v_a_7414_,
            v_a_7415_,
            v_a_7416_,
        );
    crate::leanh::lean_dec(v_a_7416_);
    crate::leanh::lean_dec_ref(v_a_7415_);
    crate::leanh::lean_dec(v_a_7414_);
    crate::leanh::lean_dec_ref(v_a_7413_);
    crate::leanh::lean_dec(v_a_7412_);
    crate::leanh::lean_dec(v_a_7411_);
    return v_res_7418_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(
    mut v___x_7419_: *mut crate::leanh::LeanObject,
    mut v_x_7420_: *mut crate::leanh::LeanObject,
    mut v___y_7421_: *mut crate::leanh::LeanObject,
    mut v___y_7422_: *mut crate::leanh::LeanObject,
    mut v___y_7423_: *mut crate::leanh::LeanObject,
    mut v___y_7424_: *mut crate::leanh::LeanObject,
    mut v___y_7425_: *mut crate::leanh::LeanObject,
    mut v___y_7426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7428_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_x_7420_, v___x_7419_, v___y_7421_);
    return v___x_7428_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(
    mut v___x_7429_: *mut crate::leanh::LeanObject,
    mut v_x_7430_: *mut crate::leanh::LeanObject,
    mut v___y_7431_: *mut crate::leanh::LeanObject,
    mut v___y_7432_: *mut crate::leanh::LeanObject,
    mut v___y_7433_: *mut crate::leanh::LeanObject,
    mut v___y_7434_: *mut crate::leanh::LeanObject,
    mut v___y_7435_: *mut crate::leanh::LeanObject,
    mut v___y_7436_: *mut crate::leanh::LeanObject,
    mut v___y_7437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7438_ = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(
        v___x_7429_,
        v_x_7430_,
        v___y_7431_,
        v___y_7432_,
        v___y_7433_,
        v___y_7434_,
        v___y_7435_,
        v___y_7436_,
    );
    crate::leanh::lean_dec(v___y_7436_);
    crate::leanh::lean_dec_ref(v___y_7435_);
    crate::leanh::lean_dec(v___y_7434_);
    crate::leanh::lean_dec_ref(v___y_7433_);
    crate::leanh::lean_dec(v___y_7432_);
    crate::leanh::lean_dec(v___y_7431_);
    return v_res_7438_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(
    mut v_msg_7439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7440_ = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision_default;
    v___x_7441_ = lean_panic_fn_borrowed(v___x_7440_, v_msg_7439_);
    return v___x_7441_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(
    mut v_a_7442_: *mut crate::leanh::LeanObject,
    mut v_x_7443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_7443_) == 0 {
                    v___x_7444_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0_spec__0___closed__3);
                    v___x_7445_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0_spec__1(v___x_7444_);
                    return v___x_7445_;
                } else {
                    v_key_7446_ = crate::leanh::lean_ctor_get(v_x_7443_, 0);
                    v_value_7447_ = crate::leanh::lean_ctor_get(v_x_7443_, 1);
                    v_tail_7448_ = crate::leanh::lean_ctor_get(v_x_7443_, 2);
                    v___x_7449_ = l_Lean_instBEqFVarId_beq(v_key_7446_, v_a_7442_);
                    if v___x_7449_ == 0 {
                        v_x_7443_ = v_tail_7448_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_7447_);
                        return v_value_7447_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0___boxed(
    mut v_a_7451_: *mut crate::leanh::LeanObject,
    mut v_x_7452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7453_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_7451_, v_x_7452_);
    crate::leanh::lean_dec(v_x_7452_);
    crate::leanh::lean_dec(v_a_7451_);
    return v_res_7453_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(
    mut v_m_7454_: *mut crate::leanh::LeanObject,
    mut v_a_7455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: u64 = 0;
    let mut v___x_7459_: u64 = 0;
    let mut v___x_7460_: u64 = 0;
    let mut v_fold_7461_: u64 = 0;
    let mut v___x_7462_: u64 = 0;
    let mut v___x_7463_: u64 = 0;
    let mut v___x_7464_: u64 = 0;
    let mut v___x_7465_: usize = 0;
    let mut v___x_7466_: usize = 0;
    let mut v___x_7467_: usize = 0;
    let mut v___x_7468_: usize = 0;
    let mut v___x_7469_: usize = 0;
    let mut v___x_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_7456_ = crate::leanh::lean_ctor_get(v_m_7454_, 1);
    v___x_7457_ = lean_array_get_size(v_buckets_7456_);
    v___x_7458_ = l_Lean_instHashableFVarId_hash(v_a_7455_);
    v___x_7459_ = 32u64;
    v___x_7460_ = lean_uint64_shift_right(v___x_7458_, v___x_7459_);
    v_fold_7461_ = lean_uint64_xor(v___x_7458_, v___x_7460_);
    v___x_7462_ = 16u64;
    v___x_7463_ = lean_uint64_shift_right(v_fold_7461_, v___x_7462_);
    v___x_7464_ = lean_uint64_xor(v_fold_7461_, v___x_7463_);
    v___x_7465_ = lean_uint64_to_usize(v___x_7464_);
    v___x_7466_ = lean_usize_of_nat(v___x_7457_);
    v___x_7467_ = 1usize;
    v___x_7468_ = lean_usize_sub(v___x_7466_, v___x_7467_);
    v___x_7469_ = lean_usize_land(v___x_7465_, v___x_7468_);
    v___x_7470_ = lean_array_uget_borrowed(v_buckets_7456_, v___x_7469_);
    v___x_7471_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0_spec__0(v_a_7455_, v___x_7470_);
    return v___x_7471_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(
    mut v_m_7472_: *mut crate::leanh::LeanObject,
    mut v_a_7473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_m_7472_, v_a_7473_);
    crate::leanh::lean_dec(v_a_7473_);
    crate::leanh::lean_dec_ref(v_m_7472_);
    return v_res_7474_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_float(
    mut v_decl_7475_: *mut crate::leanh::LeanObject,
    mut v_a_7476_: *mut crate::leanh::LeanObject,
    mut v_a_7477_: *mut crate::leanh::LeanObject,
    mut v_a_7478_: *mut crate::leanh::LeanObject,
    mut v_a_7479_: *mut crate::leanh::LeanObject,
    mut v_a_7480_: *mut crate::leanh::LeanObject,
    mut v_a_7481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7487_: u8 = 0;
    let mut v___x_7488_: u8 = 0;
    let mut v___x_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7495_: u8 = 0;
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newArms_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7501_: u8 = 0;
    let mut v___x_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7515_: u8 = 0;
    let mut v_isSharedCheck_7516_: u8 = 0;
    let mut v_unused_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7541_: u8 = 0;
    let mut v_unused_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7483_ = lean_st_ref_get(v_a_7476_);
                v_decision_7484_ = crate::leanh::lean_ctor_get(v___x_7483_, 0);
                v_isSharedCheck_7541_ = (!crate::leanh::lean_is_exclusive(v___x_7483_)) as u8;
                if v_isSharedCheck_7541_ == 0 {
                    v_unused_7542_ = crate::leanh::lean_ctor_get(v___x_7483_, 1);
                    crate::leanh::lean_dec(v_unused_7542_);
                    v___x_7486_ = v___x_7483_;
                    v_isShared_7487_ = v_isSharedCheck_7541_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decision_7484_);
                    crate::leanh::lean_dec(v___x_7483_);
                    v___x_7486_ = crate::leanh::lean_box(0);
                    v_isShared_7487_ = v_isSharedCheck_7541_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7488_ = 0;
                v___x_7489_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_7475_);
                v___x_7490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_7484_, v___x_7489_);
                crate::leanh::lean_dec(v___x_7489_);
                crate::leanh::lean_dec_ref(v_decision_7484_);
                crate::leanh::lean_inc(v___x_7490_);
                v___f_7518_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed
                        as *mut core::ffi::c_void,
                    9,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_7518_, 0, v___x_7490_);
                match crate::leanh::lean_obj_tag(v_decl_7475_) {
                    0 => {
                        v_decl_7519_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        crate::leanh::lean_inc_ref(v_decl_7519_);
                        v___x_7520_ = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(v___x_7488_, v___f_7518_, v_decl_7519_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_, v_a_7480_, v_a_7481_);
                        v___y_7492_ = v___x_7520_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_decl_7521_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        crate::leanh::lean_inc_ref(v_decl_7521_);
                        v___x_7522_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_7488_, v___f_7518_, v_decl_7521_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_, v_a_7480_, v_a_7481_);
                        v___y_7492_ = v___x_7522_;
                        state = 2;
                        continue;
                    }
                    2 => {
                        v_decl_7523_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        crate::leanh::lean_inc_ref(v_decl_7523_);
                        v___x_7524_ = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__2(v___x_7488_, v___f_7518_, v_decl_7523_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_, v_a_7480_, v_a_7481_);
                        v___y_7492_ = v___x_7524_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_fvarId_7525_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        v_y_7526_ = crate::leanh::lean_ctor_get(v_decl_7475_, 2);
                        crate::leanh::lean_inc(v___x_7490_);
                        crate::leanh::lean_inc(v_fvarId_7525_);
                        v___x_7527_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_7525_, v___x_7490_, v_a_7476_);
                        crate::leanh::lean_dec_ref(v___x_7527_);
                        crate::leanh::lean_inc(v_y_7526_);
                        v___x_7528_ = l_Lean_Compiler_LCNF_Arg_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__3___redArg(v___f_7518_, v_y_7526_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_, v_a_7480_, v_a_7481_);
                        v___y_7492_ = v___x_7528_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        crate::leanh::lean_dec_ref(v___f_7518_);
                        v_fvarId_7529_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        v_y_7530_ = crate::leanh::lean_ctor_get(v_decl_7475_, 2);
                        crate::leanh::lean_inc_n(v___x_7490_, 2);
                        crate::leanh::lean_inc(v_fvarId_7529_);
                        v___x_7531_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_7529_, v___x_7490_, v_a_7476_);
                        crate::leanh::lean_dec_ref(v___x_7531_);
                        crate::leanh::lean_inc(v_y_7530_);
                        v___x_7532_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_7530_, v___x_7490_, v_a_7476_);
                        v___y_7492_ = v___x_7532_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_fvarId_7533_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        v_y_7534_ = crate::leanh::lean_ctor_get(v_decl_7475_, 3);
                        v_ty_7535_ = crate::leanh::lean_ctor_get(v_decl_7475_, 4);
                        crate::leanh::lean_inc_n(v___x_7490_, 2);
                        crate::leanh::lean_inc(v_fvarId_7533_);
                        v___x_7536_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_7533_, v___x_7490_, v_a_7476_);
                        crate::leanh::lean_dec_ref(v___x_7536_);
                        crate::leanh::lean_inc(v_y_7534_);
                        v___x_7537_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_y_7534_, v___x_7490_, v_a_7476_);
                        crate::leanh::lean_dec_ref(v___x_7537_);
                        crate::leanh::lean_inc_ref(v_ty_7535_);
                        v___x_7538_ = l_Lean_Compiler_LCNF_Expr_forFVarM___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__4(v___f_7518_, v_ty_7535_, v_a_7476_, v_a_7477_, v_a_7478_, v_a_7479_, v_a_7480_, v_a_7481_);
                        v___y_7492_ = v___x_7538_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___f_7518_);
                        v_fvarId_7539_ = crate::leanh::lean_ctor_get(v_decl_7475_, 0);
                        crate::leanh::lean_inc(v___x_7490_);
                        crate::leanh::lean_inc(v_fvarId_7539_);
                        v___x_7540_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(v_fvarId_7539_, v___x_7490_, v_a_7476_);
                        v___y_7492_ = v___x_7540_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_7492_) == 0 {
                    v_isSharedCheck_7516_ = (!crate::leanh::lean_is_exclusive(v___y_7492_)) as u8;
                    if v_isSharedCheck_7516_ == 0 {
                        v_unused_7517_ = crate::leanh::lean_ctor_get(v___y_7492_, 0);
                        crate::leanh::lean_dec(v_unused_7517_);
                        v___x_7494_ = v___y_7492_;
                        v_isShared_7495_ = v_isSharedCheck_7516_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_7492_);
                        v___x_7494_ = crate::leanh::lean_box(0);
                        v_isShared_7495_ = v_isSharedCheck_7516_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7490_);
                    crate::leanh::lean_del_object(v___x_7486_);
                    crate::leanh::lean_dec_ref(v_decl_7475_);
                    return v___y_7492_;
                }
            }
            3 => {
                v___x_7496_ = lean_st_ref_take(v_a_7476_);
                v_decision_7497_ = crate::leanh::lean_ctor_get(v___x_7496_, 0);
                v_newArms_7498_ = crate::leanh::lean_ctor_get(v___x_7496_, 1);
                v_isSharedCheck_7515_ = (!crate::leanh::lean_is_exclusive(v___x_7496_)) as u8;
                if v_isSharedCheck_7515_ == 0 {
                    v___x_7500_ = v___x_7496_;
                    v_isShared_7501_ = v_isSharedCheck_7515_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_newArms_7498_);
                    crate::leanh::lean_inc(v_decision_7497_);
                    crate::leanh::lean_dec(v___x_7496_);
                    v___x_7500_ = crate::leanh::lean_box(0);
                    v_isShared_7501_ = v_isSharedCheck_7515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_7498_, v___x_7490_);
                if v_isShared_7487_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7486_, 1);
                    crate::leanh::lean_ctor_set(v___x_7486_, 1, v___x_7502_);
                    crate::leanh::lean_ctor_set(v___x_7486_, 0, v_decl_7475_);
                    v___x_7504_ = v___x_7486_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7514_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7514_, 0, v_decl_7475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7514_, 1, v___x_7502_);
                    v___x_7504_ = v_reuseFailAlloc_7514_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7505_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(v_newArms_7498_, v___x_7490_, v___x_7504_);
                if v_isShared_7501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7500_, 1, v___x_7505_);
                    v___x_7507_ = v___x_7500_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7513_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7513_, 0, v_decision_7497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7513_, 1, v___x_7505_);
                    v___x_7507_ = v_reuseFailAlloc_7513_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7508_ = lean_st_ref_set(v_a_7476_, v___x_7507_);
                v___x_7509_ = crate::leanh::lean_box(0);
                if v_isShared_7495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7494_, 0, v___x_7509_);
                    v___x_7511_ = v___x_7494_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 0, v___x_7509_);
                    v___x_7511_ = v_reuseFailAlloc_7512_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_float___boxed(
    mut v_decl_7543_: *mut crate::leanh::LeanObject,
    mut v_a_7544_: *mut crate::leanh::LeanObject,
    mut v_a_7545_: *mut crate::leanh::LeanObject,
    mut v_a_7546_: *mut crate::leanh::LeanObject,
    mut v_a_7547_: *mut crate::leanh::LeanObject,
    mut v_a_7548_: *mut crate::leanh::LeanObject,
    mut v_a_7549_: *mut crate::leanh::LeanObject,
    mut v_a_7550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7551_ = l_Lean_Compiler_LCNF_FloatLetIn_float(
        v_decl_7543_,
        v_a_7544_,
        v_a_7545_,
        v_a_7546_,
        v_a_7547_,
        v_a_7548_,
        v_a_7549_,
    );
    crate::leanh::lean_dec(v_a_7549_);
    crate::leanh::lean_dec_ref(v_a_7548_);
    crate::leanh::lean_dec(v_a_7547_);
    crate::leanh::lean_dec_ref(v_a_7546_);
    crate::leanh::lean_dec(v_a_7545_);
    crate::leanh::lean_dec(v_a_7544_);
    return v_res_7551_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(
    mut v_as_x27_7552_: *mut crate::leanh::LeanObject,
    mut v_b_7553_: *mut crate::leanh::LeanObject,
    mut v___y_7554_: *mut crate::leanh::LeanObject,
    mut v___y_7555_: *mut crate::leanh::LeanObject,
    mut v___y_7556_: *mut crate::leanh::LeanObject,
    mut v___y_7557_: *mut crate::leanh::LeanObject,
    mut v___y_7558_: *mut crate::leanh::LeanObject,
    mut v___y_7559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decision_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: u8 = 0;
    let mut v___x_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: u8 = 0;
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: u8 = 0;
    let mut v___x_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_7552_) == 0 {
                    v___x_7561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7561_, 0, v_b_7553_);
                    return v___x_7561_;
                } else {
                    v_head_7562_ = crate::leanh::lean_ctor_get(v_as_x27_7552_, 0);
                    v_tail_7563_ = crate::leanh::lean_ctor_get(v_as_x27_7552_, 1);
                    v___x_7564_ = lean_st_ref_get(v___y_7554_);
                    v_decision_7565_ = crate::leanh::lean_ctor_get(v___x_7564_, 0);
                    crate::leanh::lean_inc_ref(v_decision_7565_);
                    crate::leanh::lean_dec(v___x_7564_);
                    v___x_7566_ = crate::leanh::lean_box(0);
                    v___x_7567_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_head_7562_);
                    v___x_7568_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_float_spec__0(v_decision_7565_, v___x_7567_);
                    crate::leanh::lean_dec(v___x_7567_);
                    crate::leanh::lean_dec_ref(v_decision_7565_);
                    v___x_7569_ = crate::leanh::lean_box(3);
                    v___x_7570_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(
                        v___x_7568_,
                        v___x_7569_,
                    );
                    if v___x_7570_ == 0 {
                        v___x_7571_ = crate::leanh::lean_box(2);
                        v___x_7572_ = l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision_beq(
                            v___x_7568_,
                            v___x_7571_,
                        );
                        crate::leanh::lean_dec(v___x_7568_);
                        if v___x_7572_ == 0 {
                            crate::leanh::lean_inc(v_head_7562_);
                            v___x_7573_ = l_Lean_Compiler_LCNF_FloatLetIn_float(
                                v_head_7562_,
                                v___y_7554_,
                                v___y_7555_,
                                v___y_7556_,
                                v___y_7557_,
                                v___y_7558_,
                                v___y_7559_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7573_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7573_, 1);
                                v_as_x27_7552_ = v_tail_7563_;
                                v_b_7553_ = v___x_7566_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_7573_;
                            }
                        } else {
                            crate::leanh::lean_inc(v_head_7562_);
                            v___x_7575_ = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(
                                v_head_7562_,
                                v___y_7554_,
                                v___y_7555_,
                                v___y_7556_,
                                v___y_7557_,
                                v___y_7558_,
                                v___y_7559_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7575_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7575_, 1);
                                v_as_x27_7552_ = v_tail_7563_;
                                v_b_7553_ = v___x_7566_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_7575_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7568_);
                        v___x_7577_ = 0;
                        v___x_7578_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(
                            v___x_7577_,
                            v_head_7562_,
                            v___y_7557_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7578_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7578_, 1);
                            v_as_x27_7552_ = v_tail_7563_;
                            v_b_7553_ = v___x_7566_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_7578_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg___boxed(
    mut v_as_x27_7580_: *mut crate::leanh::LeanObject,
    mut v_b_7581_: *mut crate::leanh::LeanObject,
    mut v___y_7582_: *mut crate::leanh::LeanObject,
    mut v___y_7583_: *mut crate::leanh::LeanObject,
    mut v___y_7584_: *mut crate::leanh::LeanObject,
    mut v___y_7585_: *mut crate::leanh::LeanObject,
    mut v___y_7586_: *mut crate::leanh::LeanObject,
    mut v___y_7587_: *mut crate::leanh::LeanObject,
    mut v___y_7588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7589_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_7580_, v_b_7581_, v___y_7582_, v___y_7583_, v___y_7584_, v___y_7585_, v___y_7586_, v___y_7587_);
    crate::leanh::lean_dec(v___y_7587_);
    crate::leanh::lean_dec_ref(v___y_7586_);
    crate::leanh::lean_dec(v___y_7585_);
    crate::leanh::lean_dec_ref(v___y_7584_);
    crate::leanh::lean_dec(v___y_7583_);
    crate::leanh::lean_dec(v___y_7582_);
    crate::leanh::lean_dec(v_as_x27_7580_);
    return v_res_7589_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(
    mut v_a_7590_: *mut crate::leanh::LeanObject,
    mut v_a_7591_: *mut crate::leanh::LeanObject,
    mut v_a_7592_: *mut crate::leanh::LeanObject,
    mut v_a_7593_: *mut crate::leanh::LeanObject,
    mut v_a_7594_: *mut crate::leanh::LeanObject,
    mut v_a_7595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7601_: u8 = 0;
    let mut v___x_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7605_: u8 = 0;
    let mut v_unused_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7597_ = crate::leanh::lean_box(0);
                v___x_7598_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_a_7591_, v___x_7597_, v_a_7590_, v_a_7591_, v_a_7592_, v_a_7593_, v_a_7594_, v_a_7595_);
                if crate::leanh::lean_obj_tag(v___x_7598_) == 0 {
                    v_isSharedCheck_7605_ = (!crate::leanh::lean_is_exclusive(v___x_7598_)) as u8;
                    if v_isSharedCheck_7605_ == 0 {
                        v_unused_7606_ = crate::leanh::lean_ctor_get(v___x_7598_, 0);
                        crate::leanh::lean_dec(v_unused_7606_);
                        v___x_7600_ = v___x_7598_;
                        v_isShared_7601_ = v_isSharedCheck_7605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7598_);
                        v___x_7600_ = crate::leanh::lean_box(0);
                        v_isShared_7601_ = v_isSharedCheck_7605_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_7598_;
                }
            }
            1 => {
                if v_isShared_7601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7600_, 0, v___x_7597_);
                    v___x_7603_ = v___x_7600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7604_, 0, v___x_7597_);
                    v___x_7603_ = v_reuseFailAlloc_7604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases___boxed(
    mut v_a_7607_: *mut crate::leanh::LeanObject,
    mut v_a_7608_: *mut crate::leanh::LeanObject,
    mut v_a_7609_: *mut crate::leanh::LeanObject,
    mut v_a_7610_: *mut crate::leanh::LeanObject,
    mut v_a_7611_: *mut crate::leanh::LeanObject,
    mut v_a_7612_: *mut crate::leanh::LeanObject,
    mut v_a_7613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7614_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v_a_7607_, v_a_7608_, v_a_7609_, v_a_7610_, v_a_7611_, v_a_7612_);
    crate::leanh::lean_dec(v_a_7612_);
    crate::leanh::lean_dec_ref(v_a_7611_);
    crate::leanh::lean_dec(v_a_7610_);
    crate::leanh::lean_dec_ref(v_a_7609_);
    crate::leanh::lean_dec(v_a_7608_);
    crate::leanh::lean_dec(v_a_7607_);
    return v_res_7614_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(
    mut v_as_7615_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7616_: *mut crate::leanh::LeanObject,
    mut v_b_7617_: *mut crate::leanh::LeanObject,
    mut v_a_7618_: *mut crate::leanh::LeanObject,
    mut v___y_7619_: *mut crate::leanh::LeanObject,
    mut v___y_7620_: *mut crate::leanh::LeanObject,
    mut v___y_7621_: *mut crate::leanh::LeanObject,
    mut v___y_7622_: *mut crate::leanh::LeanObject,
    mut v___y_7623_: *mut crate::leanh::LeanObject,
    mut v___y_7624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7626_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(v_as_x27_7616_, v_b_7617_, v___y_7619_, v___y_7620_, v___y_7621_, v___y_7622_, v___y_7623_, v___y_7624_);
    return v___x_7626_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(
    mut v_as_7627_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7628_: *mut crate::leanh::LeanObject,
    mut v_b_7629_: *mut crate::leanh::LeanObject,
    mut v_a_7630_: *mut crate::leanh::LeanObject,
    mut v___y_7631_: *mut crate::leanh::LeanObject,
    mut v___y_7632_: *mut crate::leanh::LeanObject,
    mut v___y_7633_: *mut crate::leanh::LeanObject,
    mut v___y_7634_: *mut crate::leanh::LeanObject,
    mut v___y_7635_: *mut crate::leanh::LeanObject,
    mut v___y_7636_: *mut crate::leanh::LeanObject,
    mut v___y_7637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7638_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(v_as_7627_, v_as_x27_7628_, v_b_7629_, v_a_7630_, v___y_7631_, v___y_7632_, v___y_7633_, v___y_7634_, v___y_7635_, v___y_7636_);
    crate::leanh::lean_dec(v___y_7636_);
    crate::leanh::lean_dec_ref(v___y_7635_);
    crate::leanh::lean_dec(v___y_7634_);
    crate::leanh::lean_dec_ref(v___y_7633_);
    crate::leanh::lean_dec(v___y_7632_);
    crate::leanh::lean_dec(v___y_7631_);
    crate::leanh::lean_dec(v_as_x27_7628_);
    crate::leanh::lean_dec(v_as_7627_);
    return v_res_7638_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7639_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_7639_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__0);
    v___x_7641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7641_, 0, v___x_7640_);
    return v___x_7641_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__1);
    v___x_7643_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7644_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7644_, 0, v___x_7643_);
    crate::leanh::lean_ctor_set(v___x_7644_, 1, v___x_7643_);
    crate::leanh::lean_ctor_set(v___x_7644_, 2, v___x_7643_);
    crate::leanh::lean_ctor_set(v___x_7644_, 3, v___x_7643_);
    crate::leanh::lean_ctor_set(v___x_7644_, 4, v___x_7642_);
    crate::leanh::lean_ctor_set(v___x_7644_, 5, v___x_7642_);
    crate::leanh::lean_ctor_set(v___x_7644_, 6, v___x_7642_);
    crate::leanh::lean_ctor_set(v___x_7644_, 7, v___x_7642_);
    crate::leanh::lean_ctor_set(v___x_7644_, 8, v___x_7642_);
    crate::leanh::lean_ctor_set(v___x_7644_, 9, v___x_7642_);
    return v___x_7644_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3()
-> f64 {
    let mut v___x_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: f64 = 0.0;
    v___x_7645_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_7646_ = lean_float_of_nat(v___x_7645_);
    return v___x_7646_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(
    mut v_cls_7650_: *mut crate::leanh::LeanObject,
    mut v_msg_7651_: *mut crate::leanh::LeanObject,
    mut v___y_7652_: *mut crate::leanh::LeanObject,
    mut v___y_7653_: *mut crate::leanh::LeanObject,
    mut v___y_7654_: *mut crate::leanh::LeanObject,
    mut v___y_7655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7665_: u8 = 0;
    let mut v_env_7666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7670_: u8 = 0;
    let mut v___x_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7684_: u8 = 0;
    let mut v_tid_7685_: u64 = 0;
    let mut v_traces_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7689_: u8 = 0;
    let mut v___x_7690_: u8 = 0;
    let mut v___x_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: f64 = 0.0;
    let mut v___x_7697_: u8 = 0;
    let mut v___x_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7716_: u8 = 0;
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut v_isSharedCheck_7718_: u8 = 0;
    let mut v_unused_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7720_: u8 = 0;
    let mut v_a_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7724_: u8 = 0;
    let mut v___x_7726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_7657_ = crate::leanh::lean_ctor_get(v___y_7654_, 2);
                v_ref_7658_ = crate::leanh::lean_ctor_get(v___y_7654_, 5);
                v___x_7659_ = lean_st_ref_get(v___y_7655_);
                v___x_7660_ = lean_st_ref_get(v___y_7653_);
                v___x_7661_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_7652_);
                if crate::leanh::lean_obj_tag(v___x_7661_) == 0 {
                    v_a_7662_ = crate::leanh::lean_ctor_get(v___x_7661_, 0);
                    v_isSharedCheck_7720_ = (!crate::leanh::lean_is_exclusive(v___x_7661_)) as u8;
                    if v_isSharedCheck_7720_ == 0 {
                        v___x_7664_ = v___x_7661_;
                        v_isShared_7665_ = v_isSharedCheck_7720_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7662_);
                        crate::leanh::lean_dec(v___x_7661_);
                        v___x_7664_ = crate::leanh::lean_box(0);
                        v_isShared_7665_ = v_isSharedCheck_7720_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7660_);
                    crate::leanh::lean_dec(v___x_7659_);
                    crate::leanh::lean_dec_ref(v_msg_7651_);
                    crate::leanh::lean_dec(v_cls_7650_);
                    v_a_7721_ = crate::leanh::lean_ctor_get(v___x_7661_, 0);
                    v_isSharedCheck_7728_ = (!crate::leanh::lean_is_exclusive(v___x_7661_)) as u8;
                    if v_isSharedCheck_7728_ == 0 {
                        v___x_7723_ = v___x_7661_;
                        v_isShared_7724_ = v_isSharedCheck_7728_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7721_);
                        crate::leanh::lean_dec(v___x_7661_);
                        v___x_7723_ = crate::leanh::lean_box(0);
                        v_isShared_7724_ = v_isSharedCheck_7728_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_7666_ = crate::leanh::lean_ctor_get(v___x_7659_, 0);
                crate::leanh::lean_inc_ref(v_env_7666_);
                crate::leanh::lean_dec(v___x_7659_);
                v_lctx_7667_ = crate::leanh::lean_ctor_get(v___x_7660_, 0);
                v_isSharedCheck_7718_ = (!crate::leanh::lean_is_exclusive(v___x_7660_)) as u8;
                if v_isSharedCheck_7718_ == 0 {
                    v_unused_7719_ = crate::leanh::lean_ctor_get(v___x_7660_, 1);
                    crate::leanh::lean_dec(v_unused_7719_);
                    v___x_7669_ = v___x_7660_;
                    v_isShared_7670_ = v_isSharedCheck_7718_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_7667_);
                    crate::leanh::lean_dec(v___x_7660_);
                    v___x_7669_ = crate::leanh::lean_box(0);
                    v_isShared_7670_ = v_isSharedCheck_7718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__2);
                v___x_7672_ = lean_st_ref_take(v___y_7655_);
                v_traceState_7673_ = crate::leanh::lean_ctor_get(v___x_7672_, 4);
                v_env_7674_ = crate::leanh::lean_ctor_get(v___x_7672_, 0);
                v_nextMacroScope_7675_ = crate::leanh::lean_ctor_get(v___x_7672_, 1);
                v_ngen_7676_ = crate::leanh::lean_ctor_get(v___x_7672_, 2);
                v_auxDeclNGen_7677_ = crate::leanh::lean_ctor_get(v___x_7672_, 3);
                v_cache_7678_ = crate::leanh::lean_ctor_get(v___x_7672_, 5);
                v_messages_7679_ = crate::leanh::lean_ctor_get(v___x_7672_, 6);
                v_infoState_7680_ = crate::leanh::lean_ctor_get(v___x_7672_, 7);
                v_snapshotTasks_7681_ = crate::leanh::lean_ctor_get(v___x_7672_, 8);
                v_isSharedCheck_7717_ = (!crate::leanh::lean_is_exclusive(v___x_7672_)) as u8;
                if v_isSharedCheck_7717_ == 0 {
                    v___x_7683_ = v___x_7672_;
                    v_isShared_7684_ = v_isSharedCheck_7717_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7681_);
                    crate::leanh::lean_inc(v_infoState_7680_);
                    crate::leanh::lean_inc(v_messages_7679_);
                    crate::leanh::lean_inc(v_cache_7678_);
                    crate::leanh::lean_inc(v_traceState_7673_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7677_);
                    crate::leanh::lean_inc(v_ngen_7676_);
                    crate::leanh::lean_inc(v_nextMacroScope_7675_);
                    crate::leanh::lean_inc(v_env_7674_);
                    crate::leanh::lean_dec(v___x_7672_);
                    v___x_7683_ = crate::leanh::lean_box(0);
                    v_isShared_7684_ = v_isSharedCheck_7717_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_7685_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_7673_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_7686_ = crate::leanh::lean_ctor_get(v_traceState_7673_, 0);
                v_isSharedCheck_7716_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_7673_)) as u8;
                if v_isSharedCheck_7716_ == 0 {
                    v___x_7688_ = v_traceState_7673_;
                    v_isShared_7689_ = v_isSharedCheck_7716_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_7686_);
                    crate::leanh::lean_dec(v_traceState_7673_);
                    v___x_7688_ = crate::leanh::lean_box(0);
                    v_isShared_7689_ = v_isSharedCheck_7716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7690_ = (crate::leanh::lean_unbox(v_a_7662_) as u8);
                crate::leanh::lean_dec(v_a_7662_);
                v___x_7691_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_7667_, v___x_7690_);
                crate::leanh::lean_dec_ref(v_lctx_7667_);
                crate::leanh::lean_inc_ref(v_options_7657_);
                v___x_7692_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7692_, 0, v_env_7666_);
                crate::leanh::lean_ctor_set(v___x_7692_, 1, v___x_7671_);
                crate::leanh::lean_ctor_set(v___x_7692_, 2, v___x_7691_);
                crate::leanh::lean_ctor_set(v___x_7692_, 3, v_options_7657_);
                if v_isShared_7670_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7669_, 3);
                    crate::leanh::lean_ctor_set(v___x_7669_, 1, v_msg_7651_);
                    crate::leanh::lean_ctor_set(v___x_7669_, 0, v___x_7692_);
                    v___x_7694_ = v___x_7669_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7715_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 0, v___x_7692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 1, v_msg_7651_);
                    v___x_7694_ = v_reuseFailAlloc_7715_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7695_ = crate::leanh::lean_box(0);
                v___x_7696_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__3);
                v___x_7697_ = 0;
                v___x_7698_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__4;
                v___x_7699_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_7699_, 0, v_cls_7650_);
                crate::leanh::lean_ctor_set(v___x_7699_, 1, v___x_7695_);
                crate::leanh::lean_ctor_set(v___x_7699_, 2, v___x_7698_);
                crate::leanh::lean_ctor_set_float(
                    v___x_7699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_7696_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_7699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_7696_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7699_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_7697_,
                );
                v___x_7700_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___closed__5;
                v___x_7701_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7701_, 0, v___x_7699_);
                crate::leanh::lean_ctor_set(v___x_7701_, 1, v___x_7694_);
                crate::leanh::lean_ctor_set(v___x_7701_, 2, v___x_7700_);
                crate::leanh::lean_inc(v_ref_7658_);
                v___x_7702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7702_, 0, v_ref_7658_);
                crate::leanh::lean_ctor_set(v___x_7702_, 1, v___x_7701_);
                v___x_7703_ = l_Lean_PersistentArray_push___redArg(v_traces_7686_, v___x_7702_);
                if v_isShared_7689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7688_, 0, v___x_7703_);
                    v___x_7705_ = v___x_7688_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7714_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7714_, 0, v___x_7703_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_7714_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_7685_,
                    );
                    v___x_7705_ = v_reuseFailAlloc_7714_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7683_, 4, v___x_7705_);
                    v___x_7707_ = v___x_7683_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7713_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 0, v_env_7674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 1, v_nextMacroScope_7675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 2, v_ngen_7676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 3, v_auxDeclNGen_7677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 4, v___x_7705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 5, v_cache_7678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 6, v_messages_7679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 7, v_infoState_7680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7713_, 8, v_snapshotTasks_7681_);
                    v___x_7707_ = v_reuseFailAlloc_7713_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_7708_ = lean_st_ref_set(v___y_7655_, v___x_7707_);
                v___x_7709_ = crate::leanh::lean_box(0);
                if v_isShared_7665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7664_, 0, v___x_7709_);
                    v___x_7711_ = v___x_7664_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7712_, 0, v___x_7709_);
                    v___x_7711_ = v_reuseFailAlloc_7712_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7711_;
            }
            9 => {
                if v_isShared_7724_ == 0 {
                    v___x_7726_ = v___x_7723_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7727_, 0, v_a_7721_);
                    v___x_7726_ = v_reuseFailAlloc_7727_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(
    mut v_cls_7729_: *mut crate::leanh::LeanObject,
    mut v_msg_7730_: *mut crate::leanh::LeanObject,
    mut v___y_7731_: *mut crate::leanh::LeanObject,
    mut v___y_7732_: *mut crate::leanh::LeanObject,
    mut v___y_7733_: *mut crate::leanh::LeanObject,
    mut v___y_7734_: *mut crate::leanh::LeanObject,
    mut v___y_7735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7736_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_7729_, v_msg_7730_, v___y_7731_, v___y_7732_, v___y_7733_, v___y_7734_);
    crate::leanh::lean_dec(v___y_7734_);
    crate::leanh::lean_dec_ref(v___y_7733_);
    crate::leanh::lean_dec(v___y_7732_);
    crate::leanh::lean_dec_ref(v___y_7731_);
    return v_res_7736_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(
    mut v_cls_7737_: *mut crate::leanh::LeanObject,
    mut v_msg_7738_: *mut crate::leanh::LeanObject,
    mut v___y_7739_: *mut crate::leanh::LeanObject,
    mut v___y_7740_: *mut crate::leanh::LeanObject,
    mut v___y_7741_: *mut crate::leanh::LeanObject,
    mut v___y_7742_: *mut crate::leanh::LeanObject,
    mut v___y_7743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7745_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v_cls_7737_, v_msg_7738_, v___y_7740_, v___y_7741_, v___y_7742_, v___y_7743_);
    return v___x_7745_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(
    mut v_cls_7746_: *mut crate::leanh::LeanObject,
    mut v_msg_7747_: *mut crate::leanh::LeanObject,
    mut v___y_7748_: *mut crate::leanh::LeanObject,
    mut v___y_7749_: *mut crate::leanh::LeanObject,
    mut v___y_7750_: *mut crate::leanh::LeanObject,
    mut v___y_7751_: *mut crate::leanh::LeanObject,
    mut v___y_7752_: *mut crate::leanh::LeanObject,
    mut v___y_7753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7754_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(v_cls_7746_, v_msg_7747_, v___y_7748_, v___y_7749_, v___y_7750_, v___y_7751_, v___y_7752_);
    crate::leanh::lean_dec(v___y_7752_);
    crate::leanh::lean_dec_ref(v___y_7751_);
    crate::leanh::lean_dec(v___y_7750_);
    crate::leanh::lean_dec_ref(v___y_7749_);
    crate::leanh::lean_dec(v___y_7748_);
    return v_res_7754_;
}
pub unsafe fn _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7763_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2;
    v___x_7764_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__4;
    v___x_7765_ = l_Lean_Name_append(v___x_7764_, v___x_7763_);
    return v___x_7765_;
}
pub unsafe fn _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7767_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__6;
    v___x_7768_ = l_Lean_stringToMessageData(v___x_7767_);
    return v___x_7768_;
}
pub unsafe fn _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7770_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__8;
    v___x_7771_ = l_Lean_stringToMessageData(v___x_7770_);
    return v___x_7771_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(
    mut v_code_7772_: *mut crate::leanh::LeanObject,
    mut v_a_7773_: *mut crate::leanh::LeanObject,
    mut v_a_7774_: *mut crate::leanh::LeanObject,
    mut v_a_7775_: *mut crate::leanh::LeanObject,
    mut v_a_7776_: *mut crate::leanh::LeanObject,
    mut v_a_7777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_7784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7794_: u8 = 0;
    let mut v___x_7795_: u8 = 0;
    let mut v___x_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7806_: u8 = 0;
    let mut v___x_7808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7810_: u8 = 0;
    let mut v_isSharedCheck_7811_: u8 = 0;
    let mut v_decl_7812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7822_: u8 = 0;
    let mut v___x_7823_: u8 = 0;
    let mut v___x_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7834_: u8 = 0;
    let mut v___x_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7838_: u8 = 0;
    let mut v_isSharedCheck_7839_: u8 = 0;
    let mut v_cases_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_7849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_7850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7854_: u8 = 0;
    let mut v_newArms_7855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7861_: u8 = 0;
    let mut v___x_7862_: u8 = 0;
    let mut v___x_7863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7878_: u8 = 0;
    let mut v___x_7879_: u8 = 0;
    let mut v___x_7880_: usize = 0;
    let mut v___x_7881_: usize = 0;
    let mut v___x_7882_: u8 = 0;
    let mut v___x_7883_: usize = 0;
    let mut v___x_7884_: u8 = 0;
    let mut v_isSharedCheck_7885_: u8 = 0;
    let mut v_a_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7889_: u8 = 0;
    let mut v___x_7891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7893_: u8 = 0;
    let mut v_isSharedCheck_7894_: u8 = 0;
    let mut v_a_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7898_: u8 = 0;
    let mut v___x_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7902_: u8 = 0;
    let mut v_a_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7906_: u8 = 0;
    let mut v___x_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7910_: u8 = 0;
    let mut v___x_7911_: u8 = 0;
    let mut v___x_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_7772_) {
                0 => {
                    v_decl_7779_ = crate::leanh::lean_ctor_get(v_code_7772_, 0);
                    crate::leanh::lean_inc_ref(v_decl_7779_);
                    v_k_7780_ = crate::leanh::lean_ctor_get(v_code_7772_, 1);
                    crate::leanh::lean_inc_ref(v_k_7780_);
                    crate::leanh::lean_dec_ref_known(v_code_7772_, 2);
                    v___x_7781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7781_, 0, v_decl_7779_);
                    v___x_7782_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___x_7782_, 0, v_k_7780_);
                    v___x_7783_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(
                        v___x_7781_,
                        v___x_7782_,
                        v_a_7773_,
                        v_a_7774_,
                        v_a_7775_,
                        v_a_7776_,
                        v_a_7777_,
                    );
                    return v___x_7783_;
                }
                1 => {
                    v_decl_7784_ = crate::leanh::lean_ctor_get(v_code_7772_, 0);
                    crate::leanh::lean_inc_ref(v_decl_7784_);
                    v_k_7785_ = crate::leanh::lean_ctor_get(v_code_7772_, 1);
                    crate::leanh::lean_inc_ref(v_k_7785_);
                    crate::leanh::lean_dec_ref_known(v_code_7772_, 2);
                    v_params_7786_ = crate::leanh::lean_ctor_get(v_decl_7784_, 2);
                    crate::leanh::lean_inc_ref(v_params_7786_);
                    v_type_7787_ = crate::leanh::lean_ctor_get(v_decl_7784_, 3);
                    crate::leanh::lean_inc_ref(v_type_7787_);
                    v_value_7788_ = crate::leanh::lean_ctor_get(v_decl_7784_, 4);
                    crate::leanh::lean_inc_ref(v_value_7788_);
                    v___x_7789_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___x_7789_, 0, v_value_7788_);
                    v___x_7790_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(
                        v___x_7789_,
                        v_a_7774_,
                        v_a_7775_,
                        v_a_7776_,
                        v_a_7777_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7790_) == 0 {
                        v_a_7791_ = crate::leanh::lean_ctor_get(v___x_7790_, 0);
                        v_isSharedCheck_7811_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7790_)) as u8;
                        if v_isSharedCheck_7811_ == 0 {
                            v___x_7793_ = v___x_7790_;
                            v_isShared_7794_ = v_isSharedCheck_7811_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7791_);
                            crate::leanh::lean_dec(v___x_7790_);
                            v___x_7793_ = crate::leanh::lean_box(0);
                            v_isShared_7794_ = v_isSharedCheck_7811_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_7787_);
                        crate::leanh::lean_dec_ref(v_params_7786_);
                        crate::leanh::lean_dec_ref(v_k_7785_);
                        crate::leanh::lean_dec_ref(v_decl_7784_);
                        return v___x_7790_;
                    }
                }
                2 => {
                    v_decl_7812_ = crate::leanh::lean_ctor_get(v_code_7772_, 0);
                    crate::leanh::lean_inc_ref(v_decl_7812_);
                    v_k_7813_ = crate::leanh::lean_ctor_get(v_code_7772_, 1);
                    crate::leanh::lean_inc_ref(v_k_7813_);
                    crate::leanh::lean_dec_ref_known(v_code_7772_, 2);
                    v_params_7814_ = crate::leanh::lean_ctor_get(v_decl_7812_, 2);
                    crate::leanh::lean_inc_ref(v_params_7814_);
                    v_type_7815_ = crate::leanh::lean_ctor_get(v_decl_7812_, 3);
                    crate::leanh::lean_inc_ref(v_type_7815_);
                    v_value_7816_ = crate::leanh::lean_ctor_get(v_decl_7812_, 4);
                    crate::leanh::lean_inc_ref(v_value_7816_);
                    v___x_7817_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___x_7817_, 0, v_value_7816_);
                    v___x_7818_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(
                        v___x_7817_,
                        v_a_7774_,
                        v_a_7775_,
                        v_a_7776_,
                        v_a_7777_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7818_) == 0 {
                        v_a_7819_ = crate::leanh::lean_ctor_get(v___x_7818_, 0);
                        v_isSharedCheck_7839_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7818_)) as u8;
                        if v_isSharedCheck_7839_ == 0 {
                            v___x_7821_ = v___x_7818_;
                            v_isShared_7822_ = v_isSharedCheck_7839_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7819_);
                            crate::leanh::lean_dec(v___x_7818_);
                            v___x_7821_ = crate::leanh::lean_box(0);
                            v_isShared_7822_ = v_isSharedCheck_7839_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_7815_);
                        crate::leanh::lean_dec_ref(v_params_7814_);
                        crate::leanh::lean_dec_ref(v_k_7813_);
                        crate::leanh::lean_dec_ref(v_decl_7812_);
                        return v___x_7818_;
                    }
                }
                4 => {
                    v_cases_7840_ = crate::leanh::lean_ctor_get(v_code_7772_, 0);
                    crate::leanh::lean_inc_ref_n(v_cases_7840_, 2);
                    v___x_7841_ = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(
                        v_cases_7840_,
                        v_a_7773_,
                        v_a_7774_,
                        v_a_7775_,
                        v_a_7776_,
                        v_a_7777_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7841_) == 0 {
                        v_a_7842_ = crate::leanh::lean_ctor_get(v___x_7841_, 0);
                        crate::leanh::lean_inc(v_a_7842_);
                        crate::leanh::lean_dec_ref_known(v___x_7841_, 1);
                        v___x_7843_ = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(v_cases_7840_);
                        v___x_7844_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7844_, 0, v_a_7842_);
                        crate::leanh::lean_ctor_set(v___x_7844_, 1, v___x_7843_);
                        v___x_7845_ = lean_st_mk_ref(v___x_7844_);
                        v___x_7846_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(v___x_7845_, v_a_7773_, v_a_7774_, v_a_7775_, v_a_7776_, v_a_7777_);
                        if crate::leanh::lean_obj_tag(v___x_7846_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7846_, 1);
                            v___x_7847_ = lean_st_ref_get(v___x_7845_);
                            crate::leanh::lean_dec(v___x_7845_);
                            v_typeName_7848_ = crate::leanh::lean_ctor_get(v_cases_7840_, 0);
                            v_resultType_7849_ = crate::leanh::lean_ctor_get(v_cases_7840_, 1);
                            v_discr_7850_ = crate::leanh::lean_ctor_get(v_cases_7840_, 2);
                            v_alts_7851_ = crate::leanh::lean_ctor_get(v_cases_7840_, 3);
                            v_isSharedCheck_7894_ =
                                (!crate::leanh::lean_is_exclusive(v_cases_7840_)) as u8;
                            if v_isSharedCheck_7894_ == 0 {
                                v___x_7853_ = v_cases_7840_;
                                v_isShared_7854_ = v_isSharedCheck_7894_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_alts_7851_);
                                crate::leanh::lean_inc(v_discr_7850_);
                                crate::leanh::lean_inc(v_resultType_7849_);
                                crate::leanh::lean_inc(v_typeName_7848_);
                                crate::leanh::lean_dec(v_cases_7840_);
                                v___x_7853_ = crate::leanh::lean_box(0);
                                v_isShared_7854_ = v_isSharedCheck_7894_;
                                state = 9;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_7845_);
                            crate::leanh::lean_dec_ref(v_cases_7840_);
                            crate::leanh::lean_dec_ref_known(v_code_7772_, 1);
                            v_a_7895_ = crate::leanh::lean_ctor_get(v___x_7846_, 0);
                            v_isSharedCheck_7902_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7846_)) as u8;
                            if v_isSharedCheck_7902_ == 0 {
                                v___x_7897_ = v___x_7846_;
                                v_isShared_7898_ = v_isSharedCheck_7902_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7895_);
                                crate::leanh::lean_dec(v___x_7846_);
                                v___x_7897_ = crate::leanh::lean_box(0);
                                v_isShared_7898_ = v_isSharedCheck_7902_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_cases_7840_);
                        crate::leanh::lean_dec_ref_known(v_code_7772_, 1);
                        v_a_7903_ = crate::leanh::lean_ctor_get(v___x_7841_, 0);
                        v_isSharedCheck_7910_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7841_)) as u8;
                        if v_isSharedCheck_7910_ == 0 {
                            v___x_7905_ = v___x_7841_;
                            v_isShared_7906_ = v_isSharedCheck_7910_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7903_);
                            crate::leanh::lean_dec(v___x_7841_);
                            v___x_7905_ = crate::leanh::lean_box(0);
                            v_isShared_7906_ = v_isSharedCheck_7910_;
                            state = 20;
                            continue;
                        }
                    }
                }
                _ => {
                    v___x_7911_ = 0;
                    crate::leanh::lean_inc(v_a_7773_);
                    v___x_7912_ = lean_array_mk(v_a_7773_);
                    v___x_7913_ = l_Array_reverse___redArg(v___x_7912_);
                    v___x_7914_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                        v___x_7911_,
                        v___x_7913_,
                        v_code_7772_,
                    );
                    crate::leanh::lean_dec_ref(v___x_7913_);
                    v___x_7915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7915_, 0, v___x_7914_);
                    return v___x_7915_;
                }
            },
            1 => {
                v___x_7795_ = 0;
                v___x_7796_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_7795_, v_decl_7784_, v_type_7787_, v_params_7786_, v_a_7791_, v_a_7775_);
                if crate::leanh::lean_obj_tag(v___x_7796_) == 0 {
                    v_a_7797_ = crate::leanh::lean_ctor_get(v___x_7796_, 0);
                    crate::leanh::lean_inc(v_a_7797_);
                    crate::leanh::lean_dec_ref_known(v___x_7796_, 1);
                    if v_isShared_7794_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7793_, 1);
                        crate::leanh::lean_ctor_set(v___x_7793_, 0, v_a_7797_);
                        v___x_7799_ = v___x_7793_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7802_, 0, v_a_7797_);
                        v___x_7799_ = v_reuseFailAlloc_7802_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7793_);
                    crate::leanh::lean_dec_ref(v_k_7785_);
                    v_a_7803_ = crate::leanh::lean_ctor_get(v___x_7796_, 0);
                    v_isSharedCheck_7810_ = (!crate::leanh::lean_is_exclusive(v___x_7796_)) as u8;
                    if v_isSharedCheck_7810_ == 0 {
                        v___x_7805_ = v___x_7796_;
                        v_isShared_7806_ = v_isSharedCheck_7810_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7803_);
                        crate::leanh::lean_dec(v___x_7796_);
                        v___x_7805_ = crate::leanh::lean_box(0);
                        v_isShared_7806_ = v_isSharedCheck_7810_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7800_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___x_7800_, 0, v_k_7785_);
                v___x_7801_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(
                    v___x_7799_,
                    v___x_7800_,
                    v_a_7773_,
                    v_a_7774_,
                    v_a_7775_,
                    v_a_7776_,
                    v_a_7777_,
                );
                return v___x_7801_;
            }
            3 => {
                if v_isShared_7806_ == 0 {
                    v___x_7808_ = v___x_7805_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7809_, 0, v_a_7803_);
                    v___x_7808_ = v_reuseFailAlloc_7809_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7808_;
            }
            5 => {
                v___x_7823_ = 0;
                v___x_7824_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_7823_, v_decl_7812_, v_type_7815_, v_params_7814_, v_a_7819_, v_a_7775_);
                if crate::leanh::lean_obj_tag(v___x_7824_) == 0 {
                    v_a_7825_ = crate::leanh::lean_ctor_get(v___x_7824_, 0);
                    crate::leanh::lean_inc(v_a_7825_);
                    crate::leanh::lean_dec_ref_known(v___x_7824_, 1);
                    if v_isShared_7822_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7821_, 2);
                        crate::leanh::lean_ctor_set(v___x_7821_, 0, v_a_7825_);
                        v___x_7827_ = v___x_7821_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7830_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7830_, 0, v_a_7825_);
                        v___x_7827_ = v_reuseFailAlloc_7830_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7821_);
                    crate::leanh::lean_dec_ref(v_k_7813_);
                    v_a_7831_ = crate::leanh::lean_ctor_get(v___x_7824_, 0);
                    v_isSharedCheck_7838_ = (!crate::leanh::lean_is_exclusive(v___x_7824_)) as u8;
                    if v_isSharedCheck_7838_ == 0 {
                        v___x_7833_ = v___x_7824_;
                        v_isShared_7834_ = v_isSharedCheck_7838_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7831_);
                        crate::leanh::lean_dec(v___x_7824_);
                        v___x_7833_ = crate::leanh::lean_box(0);
                        v_isShared_7834_ = v_isSharedCheck_7838_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_7828_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___x_7828_, 0, v_k_7813_);
                v___x_7829_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(
                    v___x_7827_,
                    v___x_7828_,
                    v_a_7773_,
                    v_a_7774_,
                    v_a_7775_,
                    v_a_7776_,
                    v_a_7777_,
                );
                return v___x_7829_;
            }
            7 => {
                if v_isShared_7834_ == 0 {
                    v___x_7836_ = v___x_7833_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 0, v_a_7831_);
                    v___x_7836_ = v_reuseFailAlloc_7837_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7836_;
            }
            9 => {
                v_newArms_7855_ = crate::leanh::lean_ctor_get(v___x_7847_, 1);
                crate::leanh::lean_inc_ref(v_newArms_7855_);
                crate::leanh::lean_dec(v___x_7847_);
                v___x_7856_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_7851_);
                v___x_7857_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v_newArms_7855_, v___x_7856_, v_alts_7851_, v_a_7773_, v_a_7774_, v_a_7775_, v_a_7776_, v_a_7777_);
                if crate::leanh::lean_obj_tag(v___x_7857_) == 0 {
                    v_a_7858_ = crate::leanh::lean_ctor_get(v___x_7857_, 0);
                    v_isSharedCheck_7885_ = (!crate::leanh::lean_is_exclusive(v___x_7857_)) as u8;
                    if v_isSharedCheck_7885_ == 0 {
                        v___x_7860_ = v___x_7857_;
                        v_isShared_7861_ = v_isSharedCheck_7885_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7858_);
                        crate::leanh::lean_dec(v___x_7857_);
                        v___x_7860_ = crate::leanh::lean_box(0);
                        v_isShared_7861_ = v_isSharedCheck_7885_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_newArms_7855_);
                    crate::leanh::lean_del_object(v___x_7853_);
                    crate::leanh::lean_dec_ref(v_alts_7851_);
                    crate::leanh::lean_dec(v_discr_7850_);
                    crate::leanh::lean_dec_ref(v_resultType_7849_);
                    crate::leanh::lean_dec(v_typeName_7848_);
                    crate::leanh::lean_dec_ref_known(v_code_7772_, 1);
                    v_a_7886_ = crate::leanh::lean_ctor_get(v___x_7857_, 0);
                    v_isSharedCheck_7893_ = (!crate::leanh::lean_is_exclusive(v___x_7857_)) as u8;
                    if v_isSharedCheck_7893_ == 0 {
                        v___x_7888_ = v___x_7857_;
                        v_isShared_7889_ = v_isSharedCheck_7893_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7886_);
                        crate::leanh::lean_dec(v___x_7857_);
                        v___x_7888_ = crate::leanh::lean_box(0);
                        v_isShared_7889_ = v_isSharedCheck_7893_;
                        state = 16;
                        continue;
                    }
                }
            }
            10 => {
                v___x_7862_ = 0;
                v___x_7863_ = crate::leanh::lean_box(2);
                v___x_7864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v_newArms_7855_, v___x_7863_);
                crate::leanh::lean_dec_ref(v_newArms_7855_);
                v___x_7880_ = lean_ptr_addr(v_alts_7851_);
                crate::leanh::lean_dec_ref(v_alts_7851_);
                v___x_7881_ = lean_ptr_addr(v_a_7858_);
                v___x_7882_ = lean_usize_dec_eq(v___x_7880_, v___x_7881_);
                if v___x_7882_ == 0 {
                    v___y_7878_ = v___x_7882_;
                    state = 15;
                    continue;
                } else {
                    v___x_7883_ = lean_ptr_addr(v_resultType_7849_);
                    v___x_7884_ = lean_usize_dec_eq(v___x_7883_, v___x_7883_);
                    v___y_7878_ = v___x_7884_;
                    state = 15;
                    continue;
                }
            }
            11 => {
                v___x_7867_ = lean_array_mk(v___x_7864_);
                v___x_7868_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_7862_, v___x_7867_, v___y_7866_);
                crate::leanh::lean_dec_ref(v___x_7867_);
                if v_isShared_7861_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7860_, 0, v___x_7868_);
                    v___x_7870_ = v___x_7860_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7871_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7871_, 0, v___x_7868_);
                    v___x_7870_ = v_reuseFailAlloc_7871_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7870_;
            }
            13 => {
                if v_isShared_7854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7853_, 3, v_a_7858_);
                    v___x_7874_ = v___x_7853_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7876_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7876_, 0, v_typeName_7848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7876_, 1, v_resultType_7849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7876_, 2, v_discr_7850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7876_, 3, v_a_7858_);
                    v___x_7874_ = v_reuseFailAlloc_7876_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_7875_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7875_, 0, v___x_7874_);
                v___y_7866_ = v___x_7875_;
                state = 11;
                continue;
            }
            15 => {
                if v___y_7878_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_code_7772_, 1);
                    state = 13;
                    continue;
                } else {
                    v___x_7879_ = l_Lean_instBEqFVarId_beq(v_discr_7850_, v_discr_7850_);
                    if v___x_7879_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_code_7772_, 1);
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_7858_);
                        crate::leanh::lean_del_object(v___x_7853_);
                        crate::leanh::lean_dec(v_discr_7850_);
                        crate::leanh::lean_dec_ref(v_resultType_7849_);
                        crate::leanh::lean_dec(v_typeName_7848_);
                        v___y_7866_ = v_code_7772_;
                        state = 11;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_7889_ == 0 {
                    v___x_7891_ = v___x_7888_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7892_, 0, v_a_7886_);
                    v___x_7891_ = v_reuseFailAlloc_7892_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7891_;
            }
            18 => {
                if v_isShared_7898_ == 0 {
                    v___x_7900_ = v___x_7897_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7901_, 0, v_a_7895_);
                    v___x_7900_ = v_reuseFailAlloc_7901_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7900_;
            }
            20 => {
                if v_isShared_7906_ == 0 {
                    v___x_7908_ = v___x_7905_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7909_, 0, v_a_7903_);
                    v___x_7908_ = v_reuseFailAlloc_7909_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed(
    mut v_code_7916_: *mut crate::leanh::LeanObject,
    mut v_a_7917_: *mut crate::leanh::LeanObject,
    mut v_a_7918_: *mut crate::leanh::LeanObject,
    mut v_a_7919_: *mut crate::leanh::LeanObject,
    mut v_a_7920_: *mut crate::leanh::LeanObject,
    mut v_a_7921_: *mut crate::leanh::LeanObject,
    mut v_a_7922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7923_ =
        l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(
            v_code_7916_,
            v_a_7917_,
            v_a_7918_,
            v_a_7919_,
            v_a_7920_,
            v_a_7921_,
        );
    crate::leanh::lean_dec(v_a_7921_);
    crate::leanh::lean_dec_ref(v_a_7920_);
    crate::leanh::lean_dec(v_a_7919_);
    crate::leanh::lean_dec_ref(v_a_7918_);
    crate::leanh::lean_dec(v_a_7917_);
    return v_res_7923_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(
    mut v___x_7924_: *mut crate::leanh::LeanObject,
    mut v_i_7925_: *mut crate::leanh::LeanObject,
    mut v_as_7926_: *mut crate::leanh::LeanObject,
    mut v___y_7927_: *mut crate::leanh::LeanObject,
    mut v___y_7928_: *mut crate::leanh::LeanObject,
    mut v___y_7929_: *mut crate::leanh::LeanObject,
    mut v___y_7930_: *mut crate::leanh::LeanObject,
    mut v___y_7931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: u8 = 0;
    let mut v___x_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7938_: u8 = 0;
    let mut v___x_7939_: u8 = 0;
    let mut v_a_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7953_: usize = 0;
    let mut v___x_7954_: usize = 0;
    let mut v___x_7955_: u8 = 0;
    let mut v___x_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7966_: u8 = 0;
    let mut v___x_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7970_: u8 = 0;
    let mut v___x_7971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_7979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_7980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_7981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7984_: u8 = 0;
    let mut v___x_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8001_: u8 = 0;
    let mut v___x_8003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7933_ = lean_array_get_size(v_as_7926_);
                v___x_7934_ = lean_nat_dec_lt(v_i_7925_, v___x_7933_);
                if v___x_7934_ == 0 {
                    crate::leanh::lean_dec(v_i_7925_);
                    v___x_7935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7935_, 0, v_as_7926_);
                    return v___x_7935_;
                } else {
                    v_options_7936_ = crate::leanh::lean_ctor_get(v___y_7930_, 2);
                    v_inheritedTraceOptions_7937_ = crate::leanh::lean_ctor_get(v___y_7930_, 13);
                    v_hasTrace_7938_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_7936_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_7939_ = 0;
                    v_a_7940_ = lean_array_fget_borrowed(v_as_7926_, v_i_7925_);
                    v___x_7971_ = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(v_a_7940_);
                    v___x_7972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(v___x_7924_, v___x_7971_);
                    if v_hasTrace_7938_ == 0 {
                        crate::leanh::lean_dec(v___x_7971_);
                        v___y_7974_ = v___y_7928_;
                        v___y_7975_ = v___y_7929_;
                        v___y_7976_ = v___y_7930_;
                        v___y_7977_ = v___y_7931_;
                        state = 4;
                        continue;
                    } else {
                        v___x_7982_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2;
                        v___x_7983_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5_once), _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__5);
                        v___x_7984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_7937_,
                            v_options_7936_,
                            v___x_7983_,
                        );
                        if v___x_7984_ == 0 {
                            crate::leanh::lean_dec(v___x_7971_);
                            v___y_7974_ = v___y_7928_;
                            v___y_7975_ = v___y_7929_;
                            v___y_7976_ = v___y_7930_;
                            v___y_7977_ = v___y_7931_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7_once), _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__7);
                            v___x_7986_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_7987_ = l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision_repr(
                                v___x_7971_,
                                v___x_7986_,
                            );
                            v___x_7988_ = l_Lean_MessageData_ofFormat(v___x_7987_);
                            v___x_7989_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7989_, 0, v___x_7985_);
                            crate::leanh::lean_ctor_set(v___x_7989_, 1, v___x_7988_);
                            v___x_7990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9_once), _init_l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__9);
                            v___x_7991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7991_, 0, v___x_7989_);
                            crate::leanh::lean_ctor_set(v___x_7991_, 1, v___x_7990_);
                            v___x_7992_ = l_List_lengthTR___redArg(v___x_7972_);
                            v___x_7993_ = l_Nat_reprFast(v___x_7992_);
                            v___x_7994_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7994_, 0, v___x_7993_);
                            v___x_7995_ = l_Lean_MessageData_ofFormat(v___x_7994_);
                            v___x_7996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7996_, 0, v___x_7991_);
                            crate::leanh::lean_ctor_set(v___x_7996_, 1, v___x_7995_);
                            v___x_7997_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(v___x_7982_, v___x_7996_, v___y_7928_, v___y_7929_, v___y_7930_, v___y_7931_);
                            if crate::leanh::lean_obj_tag(v___x_7997_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7997_, 1);
                                v___y_7974_ = v___y_7928_;
                                v___y_7975_ = v___y_7929_;
                                v___y_7976_ = v___y_7930_;
                                v___y_7977_ = v___y_7931_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7972_);
                                crate::leanh::lean_dec_ref(v_as_7926_);
                                crate::leanh::lean_dec(v_i_7925_);
                                v_a_7998_ = crate::leanh::lean_ctor_get(v___x_7997_, 0);
                                v_isSharedCheck_8005_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7997_)) as u8;
                                if v_isSharedCheck_8005_ == 0 {
                                    v___x_8000_ = v___x_7997_;
                                    v_isShared_8001_ = v_isSharedCheck_8005_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7998_);
                                    crate::leanh::lean_dec(v___x_7997_);
                                    v___x_8000_ = crate::leanh::lean_box(0);
                                    v_isShared_8001_ = v_isSharedCheck_8005_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_7948_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_7939_, v___y_7942_, v___y_7947_);
                crate::leanh::lean_dec_ref(v___y_7942_);
                v___x_7949_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___x_7949_, 0, v___x_7948_);
                v___x_7950_ = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(
                    v___x_7949_,
                    v___y_7945_,
                    v___y_7943_,
                    v___y_7944_,
                    v___y_7946_,
                );
                if crate::leanh::lean_obj_tag(v___x_7950_) == 0 {
                    v_a_7951_ = crate::leanh::lean_ctor_get(v___x_7950_, 0);
                    crate::leanh::lean_inc(v_a_7951_);
                    crate::leanh::lean_dec_ref_known(v___x_7950_, 1);
                    crate::leanh::lean_inc(v_a_7940_);
                    v___x_7952_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_7940_, v_a_7951_);
                    v___x_7953_ = lean_ptr_addr(v_a_7940_);
                    v___x_7954_ = lean_ptr_addr(v___x_7952_);
                    v___x_7955_ = lean_usize_dec_eq(v___x_7953_, v___x_7954_);
                    if v___x_7955_ == 0 {
                        v___x_7956_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7957_ = lean_nat_add(v_i_7925_, v___x_7956_);
                        v___x_7958_ = lean_array_fset(v_as_7926_, v_i_7925_, v___x_7952_);
                        crate::leanh::lean_dec(v_i_7925_);
                        v_i_7925_ = v___x_7957_;
                        v_as_7926_ = v___x_7958_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7952_);
                        v___x_7960_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7961_ = lean_nat_add(v_i_7925_, v___x_7960_);
                        crate::leanh::lean_dec(v_i_7925_);
                        v_i_7925_ = v___x_7961_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_as_7926_);
                    crate::leanh::lean_dec(v_i_7925_);
                    v_a_7963_ = crate::leanh::lean_ctor_get(v___x_7950_, 0);
                    v_isSharedCheck_7970_ = (!crate::leanh::lean_is_exclusive(v___x_7950_)) as u8;
                    if v_isSharedCheck_7970_ == 0 {
                        v___x_7965_ = v___x_7950_;
                        v_isShared_7966_ = v_isSharedCheck_7970_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7963_);
                        crate::leanh::lean_dec(v___x_7950_);
                        v___x_7965_ = crate::leanh::lean_box(0);
                        v_isShared_7966_ = v_isSharedCheck_7970_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7966_ == 0 {
                    v___x_7968_ = v___x_7965_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7969_, 0, v_a_7963_);
                    v___x_7968_ = v_reuseFailAlloc_7969_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7968_;
            }
            4 => {
                v___x_7978_ = lean_array_mk(v___x_7972_);
                match crate::leanh::lean_obj_tag(v_a_7940_) {
                    0 => {
                        v_code_7979_ = crate::leanh::lean_ctor_get(v_a_7940_, 2);
                        crate::leanh::lean_inc_ref(v_code_7979_);
                        v___y_7942_ = v___x_7978_;
                        v___y_7943_ = v___y_7975_;
                        v___y_7944_ = v___y_7976_;
                        v___y_7945_ = v___y_7974_;
                        v___y_7946_ = v___y_7977_;
                        v___y_7947_ = v_code_7979_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_code_7980_ = crate::leanh::lean_ctor_get(v_a_7940_, 1);
                        crate::leanh::lean_inc_ref(v_code_7980_);
                        v___y_7942_ = v___x_7978_;
                        v___y_7943_ = v___y_7975_;
                        v___y_7944_ = v___y_7976_;
                        v___y_7945_ = v___y_7974_;
                        v___y_7946_ = v___y_7977_;
                        v___y_7947_ = v_code_7980_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_code_7981_ = crate::leanh::lean_ctor_get(v_a_7940_, 0);
                        crate::leanh::lean_inc_ref(v_code_7981_);
                        v___y_7942_ = v___x_7978_;
                        v___y_7943_ = v___y_7975_;
                        v___y_7944_ = v___y_7976_;
                        v___y_7945_ = v___y_7974_;
                        v___y_7946_ = v___y_7977_;
                        v___y_7947_ = v_code_7981_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_8001_ == 0 {
                    v___x_8003_ = v___x_8000_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8004_, 0, v_a_7998_);
                    v___x_8003_ = v_reuseFailAlloc_8004_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(
    mut v___x_8006_: *mut crate::leanh::LeanObject,
    mut v_i_8007_: *mut crate::leanh::LeanObject,
    mut v_as_8008_: *mut crate::leanh::LeanObject,
    mut v___y_8009_: *mut crate::leanh::LeanObject,
    mut v___y_8010_: *mut crate::leanh::LeanObject,
    mut v___y_8011_: *mut crate::leanh::LeanObject,
    mut v___y_8012_: *mut crate::leanh::LeanObject,
    mut v___y_8013_: *mut crate::leanh::LeanObject,
    mut v___y_8014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8015_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(v___x_8006_, v_i_8007_, v_as_8008_, v___y_8009_, v___y_8010_, v___y_8011_, v___y_8012_, v___y_8013_);
    crate::leanh::lean_dec(v___y_8013_);
    crate::leanh::lean_dec_ref(v___y_8012_);
    crate::leanh::lean_dec(v___y_8011_);
    crate::leanh::lean_dec_ref(v___y_8010_);
    crate::leanh::lean_dec(v___y_8009_);
    crate::leanh::lean_dec_ref(v___x_8006_);
    return v_res_8015_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(
    mut v_f_8016_: *mut crate::leanh::LeanObject,
    mut v_v_8017_: *mut crate::leanh::LeanObject,
    mut v___y_8018_: *mut crate::leanh::LeanObject,
    mut v___y_8019_: *mut crate::leanh::LeanObject,
    mut v___y_8020_: *mut crate::leanh::LeanObject,
    mut v___y_8021_: *mut crate::leanh::LeanObject,
    mut v___y_8022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8027_: u8 = 0;
    let mut v___x_8028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8032_: u8 = 0;
    let mut v___x_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8039_: u8 = 0;
    let mut v_a_8040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8043_: u8 = 0;
    let mut v___x_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8047_: u8 = 0;
    let mut v_isSharedCheck_8048_: u8 = 0;
    let mut v___x_8049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_8017_) == 0 {
                    v_code_8024_ = crate::leanh::lean_ctor_get(v_v_8017_, 0);
                    v_isSharedCheck_8048_ = (!crate::leanh::lean_is_exclusive(v_v_8017_)) as u8;
                    if v_isSharedCheck_8048_ == 0 {
                        v___x_8026_ = v_v_8017_;
                        v_isShared_8027_ = v_isSharedCheck_8048_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_8024_);
                        crate::leanh::lean_dec(v_v_8017_);
                        v___x_8026_ = crate::leanh::lean_box(0);
                        v_isShared_8027_ = v_isSharedCheck_8048_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_8016_);
                    v___x_8049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8049_, 0, v_v_8017_);
                    return v___x_8049_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_8022_);
                crate::leanh::lean_inc_ref(v___y_8021_);
                crate::leanh::lean_inc(v___y_8020_);
                crate::leanh::lean_inc_ref(v___y_8019_);
                crate::leanh::lean_inc(v___y_8018_);
                v___x_8028_ = crate::leanh::lean_apply_7(
                    v_f_8016_,
                    v_code_8024_,
                    v___y_8018_,
                    v___y_8019_,
                    v___y_8020_,
                    v___y_8021_,
                    v___y_8022_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_8028_) == 0 {
                    v_a_8029_ = crate::leanh::lean_ctor_get(v___x_8028_, 0);
                    v_isSharedCheck_8039_ = (!crate::leanh::lean_is_exclusive(v___x_8028_)) as u8;
                    if v_isSharedCheck_8039_ == 0 {
                        v___x_8031_ = v___x_8028_;
                        v_isShared_8032_ = v_isSharedCheck_8039_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8029_);
                        crate::leanh::lean_dec(v___x_8028_);
                        v___x_8031_ = crate::leanh::lean_box(0);
                        v_isShared_8032_ = v_isSharedCheck_8039_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8026_);
                    v_a_8040_ = crate::leanh::lean_ctor_get(v___x_8028_, 0);
                    v_isSharedCheck_8047_ = (!crate::leanh::lean_is_exclusive(v___x_8028_)) as u8;
                    if v_isSharedCheck_8047_ == 0 {
                        v___x_8042_ = v___x_8028_;
                        v_isShared_8043_ = v_isSharedCheck_8047_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8040_);
                        crate::leanh::lean_dec(v___x_8028_);
                        v___x_8042_ = crate::leanh::lean_box(0);
                        v_isShared_8043_ = v_isSharedCheck_8047_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8026_, 0, v_a_8029_);
                    v___x_8034_ = v___x_8026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 0, v_a_8029_);
                    v___x_8034_ = v_reuseFailAlloc_8038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8031_, 0, v___x_8034_);
                    v___x_8036_ = v___x_8031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8037_, 0, v___x_8034_);
                    v___x_8036_ = v_reuseFailAlloc_8037_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8036_;
            }
            5 => {
                if v_isShared_8043_ == 0 {
                    v___x_8045_ = v___x_8042_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8046_, 0, v_a_8040_);
                    v___x_8045_ = v_reuseFailAlloc_8046_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg___boxed(
    mut v_f_8050_: *mut crate::leanh::LeanObject,
    mut v_v_8051_: *mut crate::leanh::LeanObject,
    mut v___y_8052_: *mut crate::leanh::LeanObject,
    mut v___y_8053_: *mut crate::leanh::LeanObject,
    mut v___y_8054_: *mut crate::leanh::LeanObject,
    mut v___y_8055_: *mut crate::leanh::LeanObject,
    mut v___y_8056_: *mut crate::leanh::LeanObject,
    mut v___y_8057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8058_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_8050_, v_v_8051_, v___y_8052_, v___y_8053_, v___y_8054_, v___y_8055_, v___y_8056_);
    crate::leanh::lean_dec(v___y_8056_);
    crate::leanh::lean_dec_ref(v___y_8055_);
    crate::leanh::lean_dec(v___y_8054_);
    crate::leanh::lean_dec_ref(v___y_8053_);
    crate::leanh::lean_dec(v___y_8052_);
    return v_res_8058_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(
    mut v_pu_8059_: u8,
    mut v_f_8060_: *mut crate::leanh::LeanObject,
    mut v_v_8061_: *mut crate::leanh::LeanObject,
    mut v___y_8062_: *mut crate::leanh::LeanObject,
    mut v___y_8063_: *mut crate::leanh::LeanObject,
    mut v___y_8064_: *mut crate::leanh::LeanObject,
    mut v___y_8065_: *mut crate::leanh::LeanObject,
    mut v___y_8066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8068_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v_f_8060_, v_v_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
    return v___x_8068_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___boxed(
    mut v_pu_8069_: *mut crate::leanh::LeanObject,
    mut v_f_8070_: *mut crate::leanh::LeanObject,
    mut v_v_8071_: *mut crate::leanh::LeanObject,
    mut v___y_8072_: *mut crate::leanh::LeanObject,
    mut v___y_8073_: *mut crate::leanh::LeanObject,
    mut v___y_8074_: *mut crate::leanh::LeanObject,
    mut v___y_8075_: *mut crate::leanh::LeanObject,
    mut v___y_8076_: *mut crate::leanh::LeanObject,
    mut v___y_8077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_8078_: u8 = 0;
    let mut v_res_8079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_8078_ = (crate::leanh::lean_unbox(v_pu_8069_) as u8);
    v_res_8079_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(v_pu_boxed_8078_, v_f_8070_, v_v_8071_, v___y_8072_, v___y_8073_, v___y_8074_, v___y_8075_, v___y_8076_);
    crate::leanh::lean_dec(v___y_8076_);
    crate::leanh::lean_dec_ref(v___y_8075_);
    crate::leanh::lean_dec(v___y_8074_);
    crate::leanh::lean_dec_ref(v___y_8073_);
    crate::leanh::lean_dec(v___y_8072_);
    return v_res_8079_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(
    mut v_decl_8081_: *mut crate::leanh::LeanObject,
    mut v_a_8082_: *mut crate::leanh::LeanObject,
    mut v_a_8083_: *mut crate::leanh::LeanObject,
    mut v_a_8084_: *mut crate::leanh::LeanObject,
    mut v_a_8085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_8089_: u8 = 0;
    let mut v_inlineAttr_x3f_8090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8093_: u8 = 0;
    let mut v___x_8094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8100_: u8 = 0;
    let mut v___x_8102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8107_: u8 = 0;
    let mut v_a_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8111_: u8 = 0;
    let mut v___x_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8115_: u8 = 0;
    let mut v_isSharedCheck_8116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_8087_ = crate::leanh::lean_ctor_get(v_decl_8081_, 0);
                v_value_8088_ = crate::leanh::lean_ctor_get(v_decl_8081_, 1);
                v_recursive_8089_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_8081_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_8090_ = crate::leanh::lean_ctor_get(v_decl_8081_, 2);
                v_isSharedCheck_8116_ = (!crate::leanh::lean_is_exclusive(v_decl_8081_)) as u8;
                if v_isSharedCheck_8116_ == 0 {
                    v___x_8092_ = v_decl_8081_;
                    v_isShared_8093_ = v_isSharedCheck_8116_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_8090_);
                    crate::leanh::lean_inc(v_value_8088_);
                    crate::leanh::lean_inc(v_toSignature_8087_);
                    crate::leanh::lean_dec(v_decl_8081_);
                    v___x_8092_ = crate::leanh::lean_box(0);
                    v_isShared_8093_ = v_isSharedCheck_8116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8094_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___closed__0;
                v___x_8095_ = crate::leanh::lean_box(0);
                v___x_8096_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0___redArg(v___x_8094_, v_value_8088_, v___x_8095_, v_a_8082_, v_a_8083_, v_a_8084_, v_a_8085_);
                if crate::leanh::lean_obj_tag(v___x_8096_) == 0 {
                    v_a_8097_ = crate::leanh::lean_ctor_get(v___x_8096_, 0);
                    v_isSharedCheck_8107_ = (!crate::leanh::lean_is_exclusive(v___x_8096_)) as u8;
                    if v_isSharedCheck_8107_ == 0 {
                        v___x_8099_ = v___x_8096_;
                        v_isShared_8100_ = v_isSharedCheck_8107_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8097_);
                        crate::leanh::lean_dec(v___x_8096_);
                        v___x_8099_ = crate::leanh::lean_box(0);
                        v_isShared_8100_ = v_isSharedCheck_8107_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8092_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_8090_);
                    crate::leanh::lean_dec_ref(v_toSignature_8087_);
                    v_a_8108_ = crate::leanh::lean_ctor_get(v___x_8096_, 0);
                    v_isSharedCheck_8115_ = (!crate::leanh::lean_is_exclusive(v___x_8096_)) as u8;
                    if v_isSharedCheck_8115_ == 0 {
                        v___x_8110_ = v___x_8096_;
                        v_isShared_8111_ = v_isSharedCheck_8115_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8108_);
                        crate::leanh::lean_dec(v___x_8096_);
                        v___x_8110_ = crate::leanh::lean_box(0);
                        v_isShared_8111_ = v_isSharedCheck_8115_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8092_, 1, v_a_8097_);
                    v___x_8102_ = v___x_8092_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8106_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8106_, 0, v_toSignature_8087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8106_, 1, v_a_8097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8106_, 2, v_inlineAttr_x3f_8090_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8106_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_recursive_8089_,
                    );
                    v___x_8102_ = v_reuseFailAlloc_8106_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8100_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8099_, 0, v___x_8102_);
                    v___x_8104_ = v___x_8099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8105_, 0, v___x_8102_);
                    v___x_8104_ = v_reuseFailAlloc_8105_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8104_;
            }
            5 => {
                if v_isShared_8111_ == 0 {
                    v___x_8113_ = v___x_8110_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8114_, 0, v_a_8108_);
                    v___x_8113_ = v_reuseFailAlloc_8114_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn___boxed(
    mut v_decl_8117_: *mut crate::leanh::LeanObject,
    mut v_a_8118_: *mut crate::leanh::LeanObject,
    mut v_a_8119_: *mut crate::leanh::LeanObject,
    mut v_a_8120_: *mut crate::leanh::LeanObject,
    mut v_a_8121_: *mut crate::leanh::LeanObject,
    mut v_a_8122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8123_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(
        v_decl_8117_,
        v_a_8118_,
        v_a_8119_,
        v_a_8120_,
        v_a_8121_,
    );
    crate::leanh::lean_dec(v_a_8121_);
    crate::leanh::lean_dec_ref(v_a_8120_);
    crate::leanh::lean_dec(v_a_8119_);
    crate::leanh::lean_dec_ref(v_a_8118_);
    return v_res_8123_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_floatLetIn(
    mut v_decl_8124_: *mut crate::leanh::LeanObject,
    mut v_a_8125_: *mut crate::leanh::LeanObject,
    mut v_a_8126_: *mut crate::leanh::LeanObject,
    mut v_a_8127_: *mut crate::leanh::LeanObject,
    mut v_a_8128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8130_ = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(
        v_decl_8124_,
        v_a_8125_,
        v_a_8126_,
        v_a_8127_,
        v_a_8128_,
    );
    return v___x_8130_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_floatLetIn___boxed(
    mut v_decl_8131_: *mut crate::leanh::LeanObject,
    mut v_a_8132_: *mut crate::leanh::LeanObject,
    mut v_a_8133_: *mut crate::leanh::LeanObject,
    mut v_a_8134_: *mut crate::leanh::LeanObject,
    mut v_a_8135_: *mut crate::leanh::LeanObject,
    mut v_a_8136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8137_ = l_Lean_Compiler_LCNF_Decl_floatLetIn(
        v_decl_8131_,
        v_a_8132_,
        v_a_8133_,
        v_a_8134_,
        v_a_8135_,
    );
    crate::leanh::lean_dec(v_a_8135_);
    crate::leanh::lean_dec_ref(v_a_8134_);
    crate::leanh::lean_dec(v_a_8133_);
    crate::leanh::lean_dec_ref(v_a_8132_);
    return v_res_8137_;
}
pub unsafe fn l_Lean_Compiler_LCNF_floatLetIn___lam__0(
    mut v_phase_8140_: u8,
    mut v___f_8141_: *mut crate::leanh::LeanObject,
    mut v_occurrence_8142_: *mut crate::leanh::LeanObject,
    mut v_h_8143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8144_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0___closed__0;
    v___x_8145_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_8144_,
        v_phase_8140_,
        v___f_8141_,
        v_occurrence_8142_,
    );
    return v___x_8145_;
}
pub unsafe fn l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed(
    mut v_phase_8146_: *mut crate::leanh::LeanObject,
    mut v___f_8147_: *mut crate::leanh::LeanObject,
    mut v_occurrence_8148_: *mut crate::leanh::LeanObject,
    mut v_h_8149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_8150_: u8 = 0;
    let mut v_res_8151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_8150_ = (crate::leanh::lean_unbox(v_phase_8146_) as u8);
    v_res_8151_ = l_Lean_Compiler_LCNF_floatLetIn___lam__0(
        v_phase_boxed_8150_,
        v___f_8147_,
        v_occurrence_8148_,
        v_h_8149_,
    );
    return v_res_8151_;
}
pub unsafe fn l_Lean_Compiler_LCNF_floatLetIn(
    mut v_phase_8153_: u8,
    mut v_occurrence_8154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_8155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8159_: u8 = 0;
    let mut v___x_8160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_8155_ = l_Lean_Compiler_LCNF_floatLetIn___closed__0;
    v___x_8156_ = crate::leanh::lean_box((v_phase_8153_) as usize);
    v___f_8157_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_floatLetIn___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_8157_, 0, v___x_8156_);
    crate::leanh::lean_closure_set(v___f_8157_, 1, v___f_8155_);
    crate::leanh::lean_closure_set(v___f_8157_, 2, v_occurrence_8154_);
    v___x_8158_ = l_Lean_Compiler_LCNF_instInhabitedPass;
    v___x_8159_ = 0;
    v___x_8160_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
        v___x_8158_,
        v_phase_8153_,
        v___x_8159_,
        v___f_8157_,
    );
    return v___x_8160_;
}
pub unsafe fn l_Lean_Compiler_LCNF_floatLetIn___boxed(
    mut v_phase_8161_: *mut crate::leanh::LeanObject,
    mut v_occurrence_8162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_8163_: u8 = 0;
    let mut v_res_8164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_8163_ = (crate::leanh::lean_unbox(v_phase_8161_) as u8);
    v_res_8164_ = l_Lean_Compiler_LCNF_floatLetIn(v_phase_boxed_8163_, v_occurrence_8162_);
    return v_res_8164_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8216_ = crate::leanh::lean_unsigned_to_nat(3411573818);
    v___x_8217_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
    v___x_8218_ = l_Lean_Name_num___override(v___x_8217_, v___x_8216_);
    return v___x_8218_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8220_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
    v___x_8221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
    v___x_8222_ = l_Lean_Name_str___override(v___x_8221_, v___x_8220_);
    return v___x_8222_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8224_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_;
    v___x_8225_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
    v___x_8226_ = l_Lean_Name_str___override(v___x_8225_, v___x_8224_);
    return v___x_8226_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8227_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_8228_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
    v___x_8229_ = l_Lean_Name_num___override(v___x_8228_, v___x_8227_);
    return v___x_8229_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8232_: u8 = 0;
    let mut v___x_8233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8231_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___closed__2;
    v___x_8232_ = 1;
    v___x_8233_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_);
    v___x_8234_ = l_Lean_registerTraceClass(v___x_8231_, v___x_8232_, v___x_8233_);
    return v___x_8234_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2____boxed(
    mut v_a_8235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8236_ = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
    return v_res_8236_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_FloatLetIn_3411573818____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_FloatLetIn(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_FloatLetIn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
}
